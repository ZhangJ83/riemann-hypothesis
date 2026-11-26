import Lean

open Lean Meta Elab Command

set_option debug.skipKernelTC false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace ProofOpt.Typed

abbrev Pair := Expr × Expr

private def closed (e : Expr) : Bool :=
  !e.hasLooseBVars && !e.hasFVar && !e.hasMVar

-- Matching constructor spines only. Binder names/annotations are preserved from
-- the left input, not treated as data holes. All differing leaves must be closed.
private def children (a b : Expr) : Option (Array Pair) :=
  match a, b with
  | .app f x, .app g y => some #[(f,g),(x,y)]
  | .lam _ t v _, .lam _ u w _ => some #[(t,u),(v,w)]
  | .forallE _ t v _, .forallE _ u w _ => some #[(t,u),(v,w)]
  | .letE _ t x v _, .letE _ u y w _ => some #[(t,u),(x,y),(v,w)]
  | .proj n i x, .proj m j y => if n == m && i == j then some #[(x,y)] else none
  | _, _ => none

private def rebuild (a : Expr) (xs : Array Expr) : Expr :=
  match a with
  | .app .. => .app xs[0]! xs[1]!
  | .lam n _ _ bi => .lam n xs[0]! xs[1]! bi
  | .forallE n _ _ bi => .forallE n xs[0]! xs[1]! bi
  | .letE n _ _ _ nd => .letE n xs[0]! xs[1]! xs[2]! nd
  | .proj n i _ => .proj n i xs[0]!
  | _ => a

private structure Census where
  seen : Std.HashSet Pair := {}
  holes : Array Pair := #[]

private abbrev Search := StateT Census (Except String)

private partial def discover (a b : Expr) (depth : Nat := 0) : Search Unit := do
  if depth > 128 then throw "depth budget"
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return
  let k := (a,b)
  let s ← get
  if s.seen.contains k then return
  if s.seen.size >= 20000 then throw "pair budget"
  modify fun s => { s with seen := s.seen.insert k }
  if let some cs := children a b then
    for (x,y) in cs do discover x y (depth+1)
  else
    unless closed a && closed b do throw "open mismatch"
    if (← get).holes.size >= 8 then throw "hole budget"
    modify fun s => { s with holes := s.holes.push k }

private abbrev Memo := Std.HashMap Pair Expr
private abbrev Build := StateT Memo (Except String)

-- A difference is replaced only by its ordered pair, never by one side alone.
-- This avoids conflating (a,b) with (a,c), even inside dependent types.
private partial def build (params : Array (Pair × Expr)) (a b : Expr)
    (depth : Nat := 0) : Build Expr := do
  if depth > 128 then throw "rebuild depth budget"
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return a
  let k := (a,b)
  if let some v := (← get)[k]? then return v
  if (← get).size >= 20000 then throw "rebuild pair budget"
  let e ← match params.find? (fun p => p.1 == k) with
    | some p => pure p.2
    | none => do
      let some cs := children a b | throw "unbound difference in parameter type"
      let mut xs := #[]
      for (x,y) in cs do xs := xs.push (← build params x y (depth+1))
      pure (rebuild a xs)
  modify fun s => s.insert k e
  return e

private def assemble (ps : Array (Pair × Expr)) (a b : Expr) : Except String Expr :=
  ((build ps a b).run {}).map Prod.fst

private def fromExcept (x : Except String α) : MetaM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError "{e}"

private structure Plan where
  typ : Expr
  proof : Expr
  argsL : Array Expr
  argsR : Array Expr

-- Topologically schedule parameters by the differences in their inferred types.
-- No unification variables are introduced. When neither side admits a common
-- type using the already bound pairs, reject instead of guessing a transport.
private partial def bindHoles (pending : Array Pair)
    (ps : Array (Pair × Expr)) (typePair proofPair : Pair) : MetaM Plan := do
  if pending.isEmpty then
    let typ ← fromExcept (assemble ps typePair.1 typePair.2)
    let val ← fromExcept (assemble ps proofPair.1 proofPair.2)
    unless ← isProp typ do throwError "generalized result is not a proposition"
    let inferred ← inferType val
    unless ← isDefEq inferred typ do throwError "generalized body/type mismatch"
    let xs := ps.map Prod.snd
    let t ← mkForallFVars xs typ
    let v ← mkLambdaFVars xs val
    unless closed t && closed v do throwError "generalized declaration is not closed"
    return { typ := t, proof := v, argsL := ps.map (fun p => p.1.1), argsR := ps.map (fun p => p.1.2) }
  for i in [:pending.size] do
    let p := pending[i]!
    let tl ← inferType p.1
    let tr ← inferType p.2
    match assemble ps tl tr with
    | .error _ => continue
    | .ok domain =>
      if domain.hasMVar || domain.hasLooseBVars then continue
      let s ← inferType domain
      unless (← whnf s).isSort do continue
      let rest := (pending.extract 0 i) ++ (pending.extract (i+1) pending.size)
      -- Greedy order, deterministic. A kernel failure rejects the candidate;
      -- this prototype does not claim completeness over all parameter orders.
      return ← withLocalDeclD (Name.mkSimple ("p" ++ toString ps.size)) domain fun x =>
        bindHoles rest (ps.push (p,x)) typePair proofPair
  throwError "no dependency-compatible parameter order"

private def assertAllowed (n : Name) : MetaM Unit := do
  let axioms ← collectAxioms n
  for a in axioms do
    unless a == Name.mkSimple "propext" || a == (Name.mkSimple "Quot" |>.str "sound") ||
        a == (Name.mkSimple "Classical" |>.str "choice") do
      throwError "forbidden axiom {a}"

private def readTheorem (n : Name) : MetaM TheoremVal := do
  match ← getConstInfo n with
  | .thmInfo v => return v
  | _ => throwError "not a theorem: {n}"

private def mentions (e : Expr) (a b : Name) : Bool :=
  e.getUsedConstants.contains a || e.getUsedConstants.contains b

-- Each candidate is a sandbox transaction. Three *actual* theorem declarations
-- must pass Lean's kernel: the shared lemma and both original statements proved
-- using only its application. No theorem is installed into project source.
private def certify (left right certPrefix : Name) : MetaM Nat := do
  if left == right then throwError "identical source declaration"
  let l ← readTheorem left
  let r ← readTheorem right
  unless l.levelParams == r.levelParams do throwError "universe parameters differ"
  unless closed l.type && closed r.type && closed l.value && closed r.value do
    throwError "source expression not closed"
  let tp := (l.type,r.type)
  let vp := (l.value,r.value)
  let (_, census) ← fromExcept (((do
    discover tp.1 tp.2
    discover vp.1 vp.2) : Search Unit).run {})
  if census.holes.any (fun p => p == (vp.1.consumeMData,vp.2.consumeMData)) then
    throwError "whole proof hole"
  let plan ← bindHoles census.holes #[] tp vp
  -- Direct references to either original theorem cannot serve as a replacement.
  if mentions plan.typ left right || mentions plan.proof left right ||
      (plan.argsL ++ plan.argsR).any (fun e => mentions e left right) then
    throwError "direct circular replacement"
  let shared := certPrefix.str "shared"
  let a := certPrefix.str "left"
  let b := certPrefix.str "right"
  let levels := l.levelParams.map Level.param
  addDecl (.thmDecl { name := shared, levelParams := l.levelParams, type := plan.typ, value := plan.proof })
  assertAllowed shared
  for (name, typ, args) in #[(a,l.type,plan.argsL),(b,r.type,plan.argsR)] do
    let value := mkAppN (mkConst shared levels) args
    unless closed value do throwError "wrapper is not closed"
    unless ← isDefEq (← inferType value) typ do throwError "wrapper type mismatch"
    addDecl (.thmDecl { name := name, levelParams := l.levelParams, type := typ, value := value })
    assertAllowed name
  return census.holes.size

private def transaction (l r : Name) : MetaM (Except String Nat) := do
  let env ← getEnv
  try
    let certPrefix ← mkFreshUserName (Name.mkSimple "ProofOptCertificate")
    return .ok (← certify l r certPrefix)
  catch e =>
    return .error (← e.toMessageData.toString)
  finally
    setEnv env

-- Input is a pair of actual constant names; expressions are read from the
-- current imported environment rather than deserializing repr strings.
elab "#proofopt_probe " l:str r:str : command => liftTermElabM do
  let result ← transaction l.getString.toName r.getString.toName
  match result with
  | .ok holes => logInfo m!"PROOFOPT_CERTIFIED {l.getString} {r.getString} holes={holes} kernel_decls=3"
  | .error e => logInfo m!"PROOFOPT_REJECTED {l.getString} {r.getString}: {e}"

elab "#proofopt_expect " l:str r:str n:num : command => liftTermElabM do
  match ← transaction l.getString.toName r.getString.toName with
  | .ok holes =>
    unless holes == n.getNat do throwError "unexpected parameter count {holes}"
    logInfo m!"PROOFOPT_FIXTURE_PASS {l.getString} {r.getString} holes={holes}"
  | .error e => throwError "expected certification, got {e}"

elab "#proofopt_reject " l:str r:str : command => liftTermElabM do
  match ← transaction l.getString.toName r.getString.toName with
  | .ok _ => throwError "expected rejection"
  | .error _ => logInfo m!"PROOFOPT_FIXTURE_REJECT {l.getString} {r.getString}"

end ProofOpt.Typed
