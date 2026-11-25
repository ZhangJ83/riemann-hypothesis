import Lean

open Lean

-- A reference graph, not a proof exporter. Keep type references and generated
-- kernel metadata separate from editable theorem value references.
private def namesIn (e : Expr) : Std.HashSet Name := Id.run do
  let mut todo := #[e]
  let mut seen : Std.HashSet Expr := {}
  let mut names : Std.HashSet Name := {}
  while !todo.isEmpty do
    let x := todo.back!
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    match x with
    | .const n _ => names := names.insert n
    | .app f a => todo := (todo.push f).push a
    | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
    | .letE _ t v b _ => todo := ((todo.push t).push v).push b
    | .proj n _ b =>
      names := names.insert n
      todo := todo.push b
    | .mdata _ b => todo := todo.push b
    | _ => pure ()
  return names

private def kind (c : ConstantInfo) : String :=
  match c with
  | .thmInfo _ => "thm"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "ind"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .quotInfo _ => "quot"

private def kernelRefs (c : ConstantInfo) : Std.HashSet Name := Id.run do
  let mut out : Std.HashSet Name := {}
  match c with
  | .inductInfo i =>
    for n in i.all ++ i.ctors do out := out.insert n
  | .ctorInfo i => out := out.insert i.induct
  | .recInfo i =>
    for n in i.all do out := out.insert n
    for r in i.rules do
      out := out.insert r.ctor
      for n in namesIn r.rhs do out := out.insert n
  | _ => pure ()
  return out

private def jsonNames (xs : Std.HashSet Name) : Json :=
  toJson (xs.toArray.map (fun n => n.toString))

unsafe def main (args : List String) : IO UInt32 := do
  let outPath :: moduleFile :: roots := args |
    IO.eprintln "usage: lean --run KernelGraph.lean OUT.jsonl MODULES.txt ROOT..."
    return 2
  if roots.isEmpty then
    IO.eprintln "at least one root required"
    return 2
  let project : Std.HashSet Name := (← IO.FS.lines moduleFile).foldl
    (fun s l => if l.isEmpty then s else s.insert l.toName) {}
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Main }] {} (leakEnv := true)
  let modules := env.allImportedModuleNames
  let out ← IO.FS.Handle.mk outPath .write
  out.putStrLn (Json.mkObj [("record", toJson "header"), ("schema", toJson (1 : Nat)),
    ("measurement", toJson "kernel-reference-graph"), ("roots", toJson roots)]).compress
  -- Export all environment declarations, including currently unreachable ones,
  -- so replacement candidates can reference existing alternative theorems.
  let constants := env.constants.fold (init := #[]) fun acc _ c => acc.push c
  for c in constants do
    let m := match env.getModuleIdxFor? c.name with
      | some i => modules[i.toNat]!
      | none => Name.anonymous
    let t := namesIn c.type
    let v := match c.value? (allowOpaque := true) with
      | some e => namesIn e
      | none => {}
    let k := kernelRefs c
    out.putStrLn (Json.mkObj [("record", toJson "decl"), ("name", toJson c.name.toString),
      ("module", toJson m.toString), ("project", toJson (project.contains m)),
      ("kind", toJson (kind c)), ("type", jsonNames t), ("value", jsonNames v),
      ("kernel", jsonNames k)]).compress
  out.flush
  return 0
