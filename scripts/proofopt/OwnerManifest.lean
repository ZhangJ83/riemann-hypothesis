import Lean

open Lean

-- Ownership must use lossless name components, not Name.toString prefixes.
private def nameParts : Name → List Json
  | .anonymous => []
  | .str pre s => nameParts pre ++ [toJson s]
  | .num pre i => nameParts pre ++ [toJson i]

unsafe def main (args : List String) : IO UInt32 := do
  let [moduleFile, outPath] := args |
    IO.eprintln "usage: lean --run OwnerManifest.lean MODULES.txt OWNER.jsonl"
    return 2
  let project : Std.HashSet Name := (← IO.FS.lines moduleFile).foldl
    (fun s l => if l.isEmpty then s else s.insert l.toName) {}
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Main }] {} (leakEnv := true)
  let modules := env.allImportedModuleNames
  let out ← IO.FS.Handle.mk outPath .write
  let constants := env.constants.fold (init := #[]) fun acc _ c => acc.push c
  for c in constants do
    let owner := match env.getModuleIdxFor? c.name with
      | some i => toJson (project.contains modules[i.toNat]!)
      | none => Json.null
    out.putStrLn (Json.mkObj [("record", toJson "owner"),
      ("name_parts", toJson (nameParts c.name)), ("project", owner)]).compress
  out.flush
  return 0
