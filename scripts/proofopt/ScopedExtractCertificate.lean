import Lean
open Lean Meta Elab Command
set_option debug.skipKernelTC false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace ProofOpt.ScopedExtract

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

-- At the opened owner telescope, free variables are allowed but loose de
-- Bruijn variables and metavariables are not. Nested binders are opaque to
-- anti-unification; they may be retained unchanged or abstracted as a whole.
private def scoped (e : Expr) : Bool :=
  !e.hasLooseBVars && !e.hasMVar

abbrev Holes := Array (Expr × Expr)

private def anti (fuel : Nat) (a b : Expr)
    (holes : Holes) : Option (Expr × Holes) :=
  if a == b then some (a, holes) else
  match fuel with
  | 0 => none
  | k + 1 =>
    match a, b with
    | .app f x, .app g y => do
      let (f', hs) ← anti k f g holes
      let (x', hs) ← anti k x y hs
      return (.app f' x', hs)
    | _, _ => do
      if !scoped a || !scoped b then none else
      match holes.findIdx? (fun (x, y) => x == a && y == b) with
      | some i => some (.bvar i, holes)
      | none =>
        if holes.size >= 4 then none
        else some (.bvar holes.size, holes.push (a, b))

-- Every argument is loose-bvar-free; instantiate1 removes index zero and
-- decrements the other free indices, including underneath retained binders.
private def fill (template : Expr) (args : Array Expr) : Expr :=
  args.foldl (fun e x => e.instantiate1 x) template

private def headConst (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ => some n
  | _ => none

private def fragments (e : Expr) : Array Expr := Id.run do
  let mut todo := #[e]
  let mut result : Array Expr := #[]
  for _ in [:6000] do
    if todo.isEmpty || result.size >= 64 then break
    let x := todo.back!
    todo := todo.pop
    if scoped x && x.isApp && (headConst x).isSome && boundedSize x 8 >= 5 &&
        !result.contains x then
      result := result.push x
    todo := todo ++ children x
  return result

-- Old and new have no loose bvars. Exact syntactic replacement is safe
-- underneath an additional binder; kernel checking rejects ill-typed results.
private partial def replaceScoped (e old new : Expr) : Expr :=
  if e == old then new else
  match e with
  | .app f a => .app (replaceScoped f old new) (replaceScoped a old new)
  | .lam n t b bi => .lam n (replaceScoped t old new) (replaceScoped b old new) bi
  | .forallE n t b bi => .forallE n (replaceScoped t old new) (replaceScoped b old new) bi
  | .letE n t v b nd => .letE n (replaceScoped t old new) (replaceScoped v old new)
      (replaceScoped b old new) nd
  | .mdata d b => .mdata d (replaceScoped b old new)
  | .proj n i b => .proj n i (replaceScoped b old new)
  | _ => e

private def generalizeType (t : Expr) (values vars : Array Expr) : Expr := Id.run do
  let mut result := t
  for i in [:vars.size] do
    result := replaceScoped result values[i]! vars[i]!
  return result

-- Open dependent hole binders in order. Types can depend on the common
-- owner telescope and on earlier holes. Forward/cyclic dependencies are
-- not inferred. The caller certifies the resulting complete declarations.
private partial def withHoles (left right : Array Expr) (i : Nat)
    (vars : Array Expr) (k : Array Expr → MetaM Expr) : MetaM Expr := do
  if i >= left.size then return ← k vars
  let lt := generalizeType (← inferType left[i]!) left vars
  let rt := generalizeType (← inferType right[i]!) right vars
  unless scoped lt && scoped rt do throwError "open hole type"
  unless ← isDefEq lt rt do throwError "dependent hole type mismatch"
  withLocalDeclD (Name.mkSimple ("hole" ++ toString i)) lt fun v =>
    withHoles left right (i+1) (vars.push v) k

-- Local syntactic DAG diagnostic, NOT the normalized global flagship DAG.
-- Count the union of raw Expr nodes over both full declarations (and helper).
-- A saturated search is unknown, not a truncated measurement.
private def rawDag (roots : Array Expr) (cap : Nat := 200000) : Option Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut todo := roots
  while !todo.isEmpty do
    let x := todo.back!
    todo := todo.pop
    if seen.contains x then continue
    if seen.size >= cap then return none
    seen := seen.insert x
    todo := todo ++ children x
  return some seen.size

private def checked (levels : List Name) (type value : Expr) : MetaM Name := do
  unless closed type && closed value do throwError "open declaration"
  unless ← isDefEq (← inferType value) type do throwError "type mismatch"
  let n ← mkFreshUserName (Name.mkSimple "ProofOptScopedExtractCertificate")
  addDecl (.thmDecl {name := n, levelParams := levels, type := type, value := value})
  for a in ← collectAxioms n do
    unless a == Name.mkSimple "propext" || a == (Name.mkSimple "Quot" |>.str "sound") ||
        a == (Name.mkSimple "Classical" |>.str "choice") do
      throwError "forbidden axiom: {a}"
  return n

private def refs (e : Expr) (helper : Name) : Array String :=
  e.getUsedConstants.map fun n => if n == helper then "$lemma" else n.toString

private def trial (l r : TheoremVal) (xs : Array Expr) (lb rb a b template : Expr)
    (holes : Holes) (before : Option Nat) : MetaM (Json × Int) := do
  let left := holes.map Prod.fst
  let right := holes.map Prod.snd
  unless fill template left == a && fill template right == b do
    throwError "structural reconstruction failed"
  let value ← withHoles left right 0 #[] fun hs =>
    mkLambdaFVars (xs ++ hs) (fill template hs)
  let typ ← inferType value
  unless ← isProp typ do throwError "not a proof-producing abstraction"
  if (typ.getUsedConstants.contains l.name || typ.getUsedConstants.contains r.name ||
      value.getUsedConstants.contains l.name || value.getUsedConstants.contains r.name) then
    throwError "helper directly references owner"
  let helper ← checked l.levelParams typ value
  let c := mkConst helper (l.levelParams.map Level.param)
  let lv ← mkLambdaFVars xs (replaceScoped lb a (mkAppN c (xs ++ left)))
  let rv ← mkLambdaFVars xs (replaceScoped rb b (mkAppN c (xs ++ right)))
  unless lv.getUsedConstants.contains helper && rv.getUsedConstants.contains helper do
    throwError "replacement missing"
  let _ ← checked l.levelParams l.type lv
  let _ ← checked r.levelParams r.type rv
  let after := rawDag #[l.type, r.type, lv, rv, typ, value]
  let gain : Int := match before, after with
    | some u, some v => (Int.ofNat u) - (Int.ofNat v)
    | _, _ => -1000000000
  return (Json.mkObj [
    ("lemmaRefs", toJson (refs typ helper ++ refs value helper)),
    ("leftRefs", toJson (refs lv helper)),
    ("rightRefs", toJson (refs rv helper)),
    ("holeCount", toJson holes.size),
    ("scopeArity", toJson xs.size),
    ("localRawDagBefore", toJson before),
    ("localRawDagAfter", toJson after),
    ("leftFragmentSizeCapped", toJson (boundedSize a 4096)),
    ("rightFragmentSizeCapped", toJson (boundedSize b 4096)),
    ("templateSizeCapped", toJson (boundedSize value 4096))], gain)

private def search (l r : TheoremVal) (xs : Array Expr) (lb rb : Expr)
    (exact : Bool) : MetaM (Option Json) := do
  let before := rawDag #[l.type, r.type, l.value, r.value]
  if exact then
    match anti 64 lb rb #[] with
    | some (template, holes) =>
      return some (← trial l r xs lb rb lb rb template holes before).1
    | none => return none
  let mut attempts := 0
  let mut best : Option (Json × Int) := none
  let rightFragments := fragments rb
  for a in fragments lb do
    for b in rightFragments do
      if attempts >= 16 then return best.map Prod.fst
      if headConst a != headConst b then continue
      match anti 64 a b #[] with
      | some (template, holes) =>
        attempts := attempts + 1
        let state ← Meta.saveState
        try
          let candidate ← trial l r xs lb rb a b template holes before
          if best.isNone || candidate.2 > (best.getD candidate).2 then
            best := some candidate
        catch _ =>
          pure ()
        finally
          state.restore
      | none => pure ()
  return best.map Prod.fst

private def attempt (left right : Name) (exact : Bool := false) : MetaM (Option Json) := do
  if left == right then return none
  let l ← theoremVal left
  let r ← theoremVal right
  -- Conservative universe alignment. The parameter lists must be identical.
  unless l.levelParams == r.levelParams do return none
  lambdaTelescope l.value fun xs lb =>
    lambdaTelescope r.value fun ys rb => do
      unless xs.size == ys.size do return none
      for i in [:xs.size] do
        let lt ← inferType xs[i]!
        let rt := (← inferType ys[i]!).replaceFVars ys xs
        unless ← isDefEq lt rt do return none
      let rb := rb.replaceFVars ys xs
      search l r xs lb rb exact

elab "#proofopt_extract " i:num l:str r:str : command => liftTermElabM do
  match ← attempt l.getString.toName r.getString.toName with
  | some result => logInfo m!"PROOFOPT_EXTRACT_PASS {i.getNat} {Json.compress result}"
  | none => logInfo m!"PROOFOPT_EXTRACT_REJECT {i.getNat}: bounded search produced no certificate"

-- Exact-root tests exercise the transformation separately from ranking.
elab "#proofopt_extract_exact " i:num l:str r:str : command => liftTermElabM do
  match ← attempt l.getString.toName r.getString.toName true with
  | some result => logInfo m!"PROOFOPT_EXTRACT_PASS {i.getNat} {Json.compress result}"
  | none => logInfo m!"PROOFOPT_EXTRACT_REJECT {i.getNat}: incompatible telescope or structure"

end ProofOpt.ScopedExtract
