import Lean
open Lean Meta Elab Command
set_option debug.skipKernelTC false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace ProofOpt.Extract

private def theoremVal (n : Name) : MetaM TheoremVal := do
  match ← getConstInfo n with
  | .thmInfo v => return v
  | _ => throwError "not a theorem: {n}"

private def closed (e : Expr) : Bool :=
  !e.hasLooseBVars && !e.hasFVar && !e.hasMVar

private def children : Expr → Array Expr
  | .app f a => #[f, a]
  | .lam _ t b _ | .forallE _ t b _ => #[t, b]
  | .letE _ t v b _ => #[t, v, b]
  | .mdata _ b | .proj _ _ b => #[b]
  | _ => #[]

private def boundedSize (e : Expr) (cap : Nat) : Nat := Id.run do
  let mut todo := #[e]
  let mut n := 0
  for _ in [:cap] do
    if todo.isEmpty then break
    let x := todo.back!
    todo := todo.pop
    n := n + 1
    todo := todo ++ children x
  return n

-- Never traverse binders while anti-unifying: all holes and retained
-- subexpressions must be closed at the application boundary.
private def anti (fuel : Nat) (a b : Expr)
    (hole : Option (Expr × Expr)) : Option (Expr × Option (Expr × Expr)) :=
  if a == b then some (a, hole) else
  match fuel with
  | 0 => none
  | k + 1 =>
    match a, b with
    | .app f x, .app g y => do
      let (f', h) ← anti k f g hole
      let (x', h) ← anti k x y h
      return (.app f' x', h)
    | _, _ =>
      if !closed a || !closed b then none else
      match hole with
      | none => some (.bvar 0, some (a, b))
      | some (x, y) =>
        if a == x && b == y then some (.bvar 0, hole) else none

private def headConst (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ => some n
  | _ => none

private def fragments (e : Expr) : Array Expr := Id.run do
  let mut todo := #[e]
  let mut result : Array Expr := #[]
  for _ in [:4000] do
    if todo.isEmpty || result.size >= 40 then break
    let x := todo.back!
    todo := todo.pop
    if closed x && x.isApp && (headConst x).isSome && boundedSize x 8 >= 5 &&
        !result.contains x then
      result := result.push x
    todo := todo ++ children x
  return result

-- The inserted expression is closed, so no de Bruijn lifting is needed.
private partial def replaceClosed (e old new : Expr) : Expr :=
  if e == old then new else
  match e with
  | .app f a => .app (replaceClosed f old new) (replaceClosed a old new)
  | .lam n t b bi => .lam n (replaceClosed t old new) (replaceClosed b old new) bi
  | .forallE n t b bi => .forallE n (replaceClosed t old new) (replaceClosed b old new) bi
  | .letE n t v b nd => .letE n (replaceClosed t old new) (replaceClosed v old new)
      (replaceClosed b old new) nd
  | .mdata d b => .mdata d (replaceClosed b old new)
  | .proj n i b => .proj n i (replaceClosed b old new)
  | _ => e

private def checked (levels : List Name) (type value : Expr) : MetaM Name := do
  unless closed type && closed value do throwError "open declaration"
  unless ← isDefEq (← inferType value) type do throwError "type mismatch"
  let n ← mkFreshUserName (Name.mkSimple "ProofOptExtractCertificate")
  addDecl (.thmDecl {name := n, levelParams := levels, type := type, value := value})
  for a in ← collectAxioms n do
    unless a == Name.mkSimple "propext" || a == (Name.mkSimple "Quot" |>.str "sound") ||
        a == (Name.mkSimple "Classical" |>.str "choice") do
      throwError "forbidden axiom: {a}"
  return n

private def refs (e : Expr) (helper : Name) : Array String :=
  e.getUsedConstants.map fun n => if n == helper then "$lemma" else n.toString

private def trial (l r : TheoremVal) (a b template x y : Expr) : MetaM Json := do
  -- Exact reconstruction, not merely definitional equality/proof irrelevance.
  unless template.instantiate1 x == a && template.instantiate1 y == b do
    throwError "structural reconstruction failed"
  let t ← inferType x
  unless closed t do throwError "open hole type"
  unless ← isDefEq t (← inferType y) do throwError "hole type mismatch"
  let value := Expr.lam (Name.mkSimple "hole") t template .default
  let typ ← inferType value
  unless ← isProp typ do throwError "not a proof-producing abstraction"
  if (typ.getUsedConstants.contains l.name || typ.getUsedConstants.contains r.name ||
      value.getUsedConstants.contains l.name || value.getUsedConstants.contains r.name) then
    throwError "helper directly references owner"
  let helper ← checked l.levelParams typ value
  let c := mkConst helper (l.levelParams.map Level.param)
  let lv := replaceClosed l.value a (.app c x)
  let rv := replaceClosed r.value b (.app c y)
  unless lv.getUsedConstants.contains helper && rv.getUsedConstants.contains helper do
    throwError "replacement missing"
  let _ ← checked l.levelParams l.type lv
  let _ ← checked r.levelParams r.type rv
  return Json.mkObj [
    ("lemmaRefs", toJson (refs typ helper ++ refs value helper)),
    ("leftRefs", toJson (refs lv helper)),
    ("rightRefs", toJson (refs rv helper)),
    ("leftFragmentSizeCapped", toJson (boundedSize a 4096)),
    ("rightFragmentSizeCapped", toJson (boundedSize b 4096)),
    ("templateSizeCapped", toJson (boundedSize value 4096))]

private def attempt (left right : Name) : MetaM (Option Json) := do
  if left == right then return none
  let l ← theoremVal left
  let r ← theoremVal right
  -- Conservative restriction: align only identical declared universe lists.
  unless l.levelParams == r.levelParams do return none
  let mut attempts := 0
  for a in fragments l.value do
    for b in fragments r.value do
      if headConst a != headConst b || a == b then continue
      match anti 64 a b none with
      | some (template, some (x, y)) =>
        if attempts >= 8 then return none
        attempts := attempts + 1
        let state ← Meta.saveState
        try
          return some (← trial l r a b template x y)
        catch _ =>
          pure ()
        finally
          state.restore
      | _ => pure ()
  return none

elab "#proofopt_extract " i:num l:str r:str : command => liftTermElabM do
  match ← attempt l.getString.toName r.getString.toName with
  | some result => logInfo m!"PROOFOPT_EXTRACT_PASS {i.getNat} {Json.compress result}"
  | none => logInfo m!"PROOFOPT_EXTRACT_REJECT {i.getNat}: no certified abstraction in bounded search"

end ProofOpt.Extract
