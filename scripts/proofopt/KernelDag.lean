import Lean

open Lean

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
Exact syntax hash-consing for imported kernel expressions. The quotient erases
binder names, binder annotations, let nondependency hints, and metadata. It
does NOT unfold constants, apply proof irrelevance, normalize universe
arithmetic, beta-reduce, or change de Bruijn indices. Universe parameter names
are preserved. Key equality, not a digest, decides node identity.
-/
private inductive Key where
  | bvar (i : Nat)
  | sort (u : Level)
  | const (n : Name) (us : List Level)
  | app (f a : Nat)
  | lam (t b : Nat)
  | forallE (t b : Nat)
  | letE (t v b : Nat)
  | natLit (n : Nat)
  | strLit (s : String)
  | proj (n : Name) (i b : Nat)
  | invalid
  deriving BEq, Hashable, Inhabited

private def Key.children : Key → Array Nat
  | .app f a | .lam f a | .forallE f a => #[f, a]
  | .letE t v b => #[t, v, b]
  | .proj _ _ b => #[b]
  | _ => #[]

private structure Dag where
  index : Std.HashMap Key Nat := {}
  keys : Array Key := #[]
  marks : Array Nat := #[]
  -- Only per declaration; do not retain another global copy of all Exprs.
  memo : ExprStructMap Nat := {}

private def internKey (key : Key) : StateM Dag Nat :=
  modifyGet fun s =>
    match s.index[key]? with
    | some id => (id, s)
    | none =>
      let id := s.keys.size
      (id, { s with index := s.index.insert key id,
                    keys := s.keys.push key, marks := s.marks.push 0 })

private partial def intern (e : Expr) : StateM Dag Nat := do
  if let some id := (← get).memo[⟨e⟩]? then return id
  let id ← match e with
    | .bvar i => internKey (.bvar i)
    | .sort u => internKey (.sort u)
    | .const n us => internKey (.const n us)
    | .app f a => do internKey (.app (← intern f) (← intern a))
    | .lam _ t b _ => do internKey (.lam (← intern t) (← intern b))
    | .forallE _ t b _ => do internKey (.forallE (← intern t) (← intern b))
    | .letE _ t v b _ => do internKey (.letE (← intern t) (← intern v) (← intern b))
    | .lit (.natVal n) => internKey (.natLit n)
    | .lit (.strVal s) => internKey (.strLit s)
    | .proj n i b => do internKey (.proj n i (← intern b))
    | .mdata _ b => intern b
    | .fvar _ | .mvar _ => internKey .invalid
  modify fun s => { s with memo := s.memo.insert ⟨e⟩ id }
  return id

private def mark (s : Dag) (id mask : Nat) : Dag :=
  { s with marks := s.marks.set! id (s.marks[id]! ||| mask) }

private def add (s : Dag) (e : Expr) (mask : Nat) : IO (Nat × Dag) := do
  if e.hasFVar || e.hasMVar then
    throw (IO.userError "free or metavariable in imported declaration")
  let (id, next) := (intern e).run s
  return (id, mark next id mask)

private def counts (s : Dag) (n : Nat) : Array Nat × Array Nat := Id.run do
  let mut marks := s.marks
  let mut perRoot := Array.replicate (3*n) 0
  let mut unions := Array.replicate 3 0
  let stride := 2^n
  -- All children were interned before their parents. One descending pass
  -- propagates the root/category bitset down the entire shared DAG.
  for j in [:s.keys.size] do
    let id := s.keys.size - 1 - j
    let mask := marks[id]!
    for child in s.keys[id]!.children do
      marks := marks.set! child (marks[child]! ||| mask)
    for category in [:3] do
      let localMask := (mask / (stride^category)) % stride
      if localMask != 0 then
        unions := unions.set! category (unions[category]! + 1)
      for i in [:n] do
        if (localMask &&& (2^i)) != 0 then
          let pos := category*n+i
          perRoot := perRoot.set! pos (perRoot[pos]! + 1)
  return (perRoot, unions)

private def require (p : Bool) (msg : String) : IO Unit :=
  if p then pure () else throw (IO.userError msg)

private def selfTest : IO UInt32 := do
  let a := mkConst `Nat
  let b := mkConst `Bool
  let x := Expr.lam `x a (.bvar 0) .default
  let y := Expr.lam `y a (.bvar 0) .implicit
  let (xi, s) ← add {} x 1
  let (yi, s) ← add s y 1
  require (xi == yi) "binder annotation and name quotient"
  let (mi, s) ← add s (.mdata default x) 1
  require (mi == xi) "metadata erasure"
  let (li, s) ← add s (.letE `x a (.bvar 0) (.bvar 0) false) 1
  let (lj, s) ← add s (.letE `y a (.bvar 0) (.bvar 0) true) 1
  require (li == lj) "let annotations erased"
  let (fi, s) ← add s (.forallE `x a (.bvar 0) .default) 1
  require (fi != xi) "lambda and forall distinguished"
  let (u0, s) ← add s (.sort .zero) 1
  let (u1, s) ← add s (.sort (.succ .zero)) 1
  require (u0 != u1) "universe levels distinguished"
  let (c0, s) ← add s (mkConst `List [.zero]) 1
  let (c1, s) ← add s (mkConst `List [.succ .zero]) 1
  require (c0 != c1) "constant universe arguments distinguished"
  let (p0, s) ← add s (.proj `Prod 0 a) 1
  let (p1, s) ← add s (.proj `Prod 1 a) 1
  require (p0 != p1) "projection fields distinguished"
  let (n0, s) ← add s (.lit (.natVal 1)) 1
  let (n1, s) ← add s (.lit (.strVal "1")) 1
  require (n0 != n1) "literal types distinguished"
  let (ab, s) ← add s (.app a b) 1
  let (ba, _) ← add s (.app b a) 1
  require (ab != ba) "application order distinguished"
  let (_, s) ← add {} (.app a b) 21
  let (_, s) ← add s (.app a a) 2
  let (per, unions) := counts s 2
  require (per == #[3, 2, 3, 0, 3, 0]) "exact per-scope counts"
  require (unions == #[4, 3, 3]) "exact union counts and sharing"
  require (s.keys.size == 4) "no duplicate interned nodes"
  IO.println "PASS 12 Lean structural DAG assertions"
  return 0

private def readScope (path : String) (limit : Nat) :
    IO (Std.HashMap String (Nat × Bool)) := do
  let mut out : Std.HashMap String (Nat × Bool) := {}
  for line in ← IO.FS.lines path do
    let [name, rawMask, project] := line.splitOn "\t" |
      throw (IO.userError "malformed scope TSV")
    let some mask := rawMask.toNat? | throw (IO.userError "malformed bitmask")
    require (mask > 0 && mask < limit && (project == "0" || project == "1")) "invalid scope row"
    require (!out.contains name && !name.isEmpty) "duplicate or empty scope name"
    out := out.insert name (mask, project == "1")
  require (out.size > 0) "empty scope"
  return out

unsafe def main (args : List String) : IO UInt32 := do
  if args == ["--self-test"] then return ← selfTest
  let output :: scopeFile :: moduleFile :: roots := args |
    throw (IO.userError "usage: KernelDag OUT.json SCOPE.tsv MODULES.txt ROOT...")
  let n := roots.length
  require (n > 0 && n <= 10) "root count out of range"
  let stride := 2^n
  let scope ← readScope scopeFile stride
  let projectModules : Std.HashSet Name := (← IO.FS.lines moduleFile).foldl
    (fun s l => if l.isEmpty then s else s.insert l.toName) {}
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Main }] {} (leakEnv := true)
  let modules := env.allImportedModuleNames
  let constants := env.constants.fold (init := #[]) fun acc _ c => acc.push c
  let mut d : Dag := {}
  let mut matched : Std.HashSet String := {}
  let mut projectCount := 0
  let mut theoremValues := 0
  let mut recursorRules := 0
  let mut missingOpaque := 0
  let mut twins : Std.HashMap (Nat × Nat × List Name) (Array (String × String)) := {}
  for c in constants do
    let name := c.name.toString
    let some (mask, isProject) := scope[name]? | continue
    require (!matched.contains name) ("nonunique rendered declaration name " ++ name)
    matched := matched.insert name
    let m := match env.getModuleIdxFor? c.name with
      | some i => modules[i.toNat]!
      | none => Name.anonymous
    require (projectModules.contains m == isProject) ("module scope mismatch " ++ name)
    if isProject then projectCount := projectCount + 1
    let allMask := mask ||| (if isProject then mask*stride else 0)
    let (tid, dNext) ← add d c.type allMask
    d := dNext
    match c.value? (allowOpaque := true) with
    | some e =>
      let isTheorem := match c with | .thmInfo _ => true | _ => false
      let vm := allMask ||| (if isProject && isTheorem then mask*stride*stride else 0)
      let (vid, dNext) ← add d e vm
      d := dNext
      if isProject && isTheorem then
        theoremValues := theoremValues + 1
        let key := (tid, vid, c.levelParams)
        twins := twins.insert key ((twins[key]?.getD #[]).push (name, m.toString))
    | none =>
      match c with
      | .thmInfo _ | .defnInfo _ =>
        throw (IO.userError ("missing imported body: " ++ name))
      | .opaqueInfo _ => missingOpaque := missingOpaque + 1
      | _ => pure ()
    match c with
    | .recInfo info =>
      for rule in info.rules do
        let (_, next) ← add d rule.rhs allMask
        d := next
        recursorRules := recursorRules + 1
    | _ => pure ()
    d := { d with memo := {} }
  require (matched.size == scope.size) ("scope names absent from environment: " ++ toString (scope.size-matched.size))
  for root in roots do
    require (matched.contains root) ("root absent: " ++ root)
  require (!d.index.contains .invalid) "invalid expression encountered"
  let (per, unions) := counts d n
  require (unions[0]! == d.keys.size) "unmarked interned node"
  let mut groups : Array Json := #[]
  for (key, members) in twins.toArray do
    if members.size > 1 then
      let mods := members.foldl (fun (a : Std.HashSet String) x => a.insert x.2) {}
      if mods.size > 1 then
        groups := groups.push (Json.mkObj [("type_id", toJson key.1),
          ("proof_id", toJson key.2.1), ("members", toJson members)])
  let report := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("measurement", toJson "exact-quotient-imported-expression-DAG"),
    ("root_names", toJson roots),
    ("categories", toJson ["all_reachable_types_values_recursor_rhs",
      "project_reachable_types_values_recursor_rhs", "project_theorem_values_only"]),
    ("per_root_flat_category_major", toJson per), ("unions", toJson unions),
    ("reachable_declarations", toJson matched.size),
    ("project_reachable_declarations_including_roots", toJson projectCount),
    ("project_theorem_values", toJson theoremValues), ("recursor_rules", toJson recursorRules),
    ("missing_opaque_values", toJson missingOpaque),
    ("cross_module_exact_type_and_value_groups", toJson groups)]
  IO.FS.writeFile output (report.compress ++ "\n")
  IO.println ("DAG_SUMMARY " ++ (Json.mkObj [
    ("unions", toJson unions), ("per_root", toJson per), ("declarations", toJson matched.size),
    ("project_declarations", toJson projectCount), ("project_theorem_values", toJson theoremValues),
    ("missing_opaque_values", toJson missingOpaque), ("cross_module_groups", toJson groups.size)]).compress)
  return 0
