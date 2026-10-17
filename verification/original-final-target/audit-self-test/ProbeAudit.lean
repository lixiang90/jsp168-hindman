-- Intentionally no `module` header, matching CheckAllDeclarations.lean.
import ProbeModule
import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "Probe audit unexpectedly uses module-system restrictions"
  let mut found := false
  let mut privateAxiom := false
  let mut privateProof := false
  let mut exportedPrivate := false
  let mut exportedClean := false
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `ProbeModule then
      found := true
      for name in env.header.moduleData[i]!.constNames do
        unless (env.checked.get.find? name).isSome do
          throwError m!"Module constName missing from checked kernel env: {name}"
        let axioms ← collectAxioms name
        let userName := privateToUserName name
        logInfo m!"PROBE DECL: {name}; user={userName}; axioms={axioms}"
        if userName == `AuditPrivateProbe.hiddenUnusedAxiom then
          unless axioms.contains name do
            throwError "Private unused axiom did not report itself"
          privateAxiom := true
        if userName == `AuditPrivateProbe.hiddenUnusedProof then
          unless axioms.any (fun ax => privateToUserName ax == `AuditPrivateProbe.hiddenUnusedAxiom) do
            throwError "Private unused theorem lost private axiom dependency"
          privateProof := true
        if userName == `AuditPrivateProbe.exportedUsingPrivate then
          unless axioms.any (fun ax => privateToUserName ax == `AuditPrivateProbe.hiddenUsedAxiom) do
            throwError "Exported theorem lost private axiom dependency"
          exportedPrivate := true
        if userName == `AuditPrivateProbe.exportedClean then
          unless axioms.isEmpty do
            throwError "Clean theorem unexpectedly has axioms"
          exportedClean := true
  unless found && privateAxiom && privateProof && exportedPrivate && exportedClean do
    throwError "Probe did not cover every required private/public case"
  logInfo "PROBE COMPLETE: split-module private unused axioms/theorems and exported dependencies detected"
