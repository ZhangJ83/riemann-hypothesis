import Lean
open Lean Meta Elab Command
set_option debug.skipKernelTC false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace ProofOpt.Parametric

private def theoremVal (n : Name) : MetaM TheoremVal := do
  match ← getConstInfo n with
  | .thmInfo v => return v
  | _ => throwError "not a theorem: {n}"

-- Apply with fresh universe metavariables, then discharge remaining goals
-- by local assumptions. No arbitrary tactic script or untrusted input.
private def synthesize (l : TheoremVal) (right : Name) : MetaM Expr :=
  forallTelescope l.type fun xs conclusion => do
    let goal ← mkFreshExprMVar conclusion
    let pending ← goal.mvarId!.apply (← mkConstWithFreshMVarLevels right)
    let mut remaining := pending
    for _ in [:pending.length + 1] do
      let mut next : List MVarId := []
      for g in remaining do
        unless ← g.isAssigned do
          let state ← Meta.saveState
          try
            g.assumption
          catch _ =>
            state.restore
            next := g :: next
      remaining := next.reverse
      if remaining.isEmpty then break
    unless remaining.isEmpty do throwError "unresolved premises"
    let body ← instantiateMVars goal
    let value ← instantiateMVars (← mkLambdaFVars xs body)
    if value.hasMVar || value.hasFVar then throwError "open replacement"
    return value

private def certify (left right : Name) : MetaM (Array Name) := do
  if left == right then throwError "same declaration"
  let l ← theoremVal left
  let _ ← theoremVal right
  let value ← synthesize l right
  unless ← isDefEq (← inferType value) l.type do throwError "type mismatch"
  let refs := value.getUsedConstants
  unless refs.contains right do throwError "missing replacement constant"
  if refs.contains left then throwError "self reference"
  let name ← mkFreshUserName (Name.mkSimple "ProofOptParamCertificate")
  let decl : TheoremVal := {
    name := name
    levelParams := l.levelParams
    type := l.type
    value := value
  }
  addDecl (.thmDecl decl)
  for a in ← collectAxioms name do
    unless a == Name.mkSimple "propext" || a == (Name.mkSimple "Quot" |>.str "sound") ||
        a == (Name.mkSimple "Classical" |>.str "choice") do
      throwError "forbidden axiom: {a}"
  return refs

private def transaction (l r : Name) : MetaM (Except String (Array Name)) := do
  let state ← Meta.saveState
  try
    return .ok (← certify l r)
  catch e =>
    return .error (← e.toMessageData.toString)
  finally
    state.restore

elab "#proofopt_param " i:num l:str r:str : command => liftTermElabM do
  match ← transaction l.getString.toName r.getString.toName with
  | .ok refs =>
    let payload := Json.compress (toJson (refs.map Name.toString))
    logInfo m!"PROOFOPT_PARAM_PASS {i.getNat} {payload}"
  | .error e => logInfo m!"PROOFOPT_PARAM_REJECT {i.getNat}: {e}"

end ProofOpt.Parametric
