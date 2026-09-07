import Lean.Util.CollectAxioms
import ReasLib
import S2

/-!
# Project axiom audit

Checks every declaration exported by a `ReasLib.*` or `S2.*` module against
the project's accepted logical foundations.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for _h : idx in [0:env.header.moduleData.size] do
    let moduleName := env.header.moduleNames[idx]!
    let moduleString := moduleName.toString
    if moduleString == "ReasLib" || moduleString.startsWith "ReasLib." ||
        moduleString == "S2" || moduleString.startsWith "S2." ||
        moduleString == "rockafellar_sum" then
      for name in env.header.moduleData[idx].constNames do
        names := names.push name
  if names.isEmpty then
    throwError "Axiom audit selected no project declarations"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Array Name) := #[]
  for name in names do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun axiomName => !allowed.contains axiomName
    if !unexpected.isEmpty then
      bad := bad.push (name, unexpected)
  if !bad.isEmpty then
    throwError m!"Axiom audit failed for {bad.size} declaration(s): {bad.take 20}"
  logInfo m!"Axiom audit passed for {names.size} exported project declaration(s)"
