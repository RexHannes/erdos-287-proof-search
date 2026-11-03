import Lean

open Lean Elab Command

/- This body is appended after imports of EVERY local Formalisation module. -/
elab "#audit_formalisation" : command => do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let names := env.constants.toList.filterMap fun (name, _) => do
    let idx ← env.getModuleIdxFor? name
    let mod ← moduleNames[idx.toNat]?
    if (`Formalisation).isPrefixOf mod then some name else none
  let names := names.toArray.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then
    throwError "AXIOM AUDIT FAILED: no declarations in the Formalisation library"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut theoremCount := 0
  let mut failures := 0
  for name in names do
    let axioms ← Lean.collectAxioms name
    logInfo m!"AXIOMS {name}: {axioms.toList}"
    if let some (.thmInfo info) := env.find? name then
      theoremCount := theoremCount + 1
      logInfo m!"STATEMENT {name}: {info.type}"
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      failures := failures + 1
      logError m!"AXIOM AUDIT FAILED for {name}: forbidden axioms {unexpected.toList}"
  if theoremCount == 0 then
    throwError "AXIOM AUDIT FAILED: no theorem declarations were checked"
  if failures > 0 then
    throwError "AXIOM AUDIT FAILED: {failures} declaration(s) have forbidden dependencies"
  logInfo m!"AXIOM AUDIT PASSED: {names.size} declarations, {theoremCount} theorem(s)"

set_option pp.universes true in
#audit_formalisation
