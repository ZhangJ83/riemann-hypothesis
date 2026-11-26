import Lean
open Lean Meta Elab Command
set_option debug.skipKernelTC false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace ProofOpt.Alias
private def theoremVal (n : Name) : MetaM TheoremVal := do
  match ← getConstInfo n with
  | .thmInfo v => return v
  | _ => throwError "not a theorem: {n}"

private def allowedAxioms (n : Name) : MetaM Unit := do
  let axioms ← collectAxioms n
  for a in axioms do
    unless a == Name.mkSimple "propext" || a == (Name.mkSimple "Quot" |>.str "sound") ||
        a == (Name.mkSimple "Classical" |>.str "choice") do
      throwError "forbidden axiom: {a}"

-- Actual kernel declaration with the unchanged source statement.
-- It does not modify project source or establish source import visibility.
private def certify (left right : Name) : MetaM Unit := do
  if left == right then throwError "same declaration"
  let l ← theoremVal left
  let r ← theoremVal right
  unless l.levelParams.length == r.levelParams.length do
    throwError "different universe arity"
  let value := mkConst right (l.levelParams.map Level.param)
  unless ← isDefEq (← inferType value) l.type do
    throwError "replacement type does not match original statement"
  let name ← mkFreshUserName (Name.mkSimple "ProofOptAliasCertificate")
  addDecl (.thmDecl { name := name, levelParams := l.levelParams,
    type := l.type, value := value })
  allowedAxioms name

private def transaction (l r : Name) : MetaM (Except String Unit) := do
  let env ← getEnv
  try
    certify l r
    return .ok ()
  catch e =>
    return .error (← e.toMessageData.toString)
  finally
    setEnv env

elab "#proofopt_alias " i:num l:str r:str : command => liftTermElabM do
  match ← transaction l.getString.toName r.getString.toName with
  | .ok _ => logInfo m!"PROOFOPT_ALIAS_PASS {i.getNat}"
  | .error e => logInfo m!"PROOFOPT_ALIAS_REJECT {i.getNat}: {e}"

end ProofOpt.Alias
