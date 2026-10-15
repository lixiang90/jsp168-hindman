import Hindman168.OriginalSameStepLinearizationOrbit
import Hindman168.OriginalSameStepLinearizationConjugation
import Hindman168.OriginalSameStepLinearizationTaylor
import Hindman168.OriginalFiberMetricExtension
import Lean
open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let targets : List Name := [`Hindman168.OriginalSameStepLinearizationOrbit, `Hindman168.OriginalSameStepLinearizationConjugation, `Hindman168.OriginalSameStepLinearizationTaylor, `Hindman168.OriginalFiberMetricExtension]
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if targets.contains env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        let axioms ← collectAxioms name
        for ax in axioms do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError m!"Unexpected axiom {ax} in {name}"
        logInfo m!"AUDIT {name}: {axioms}"
        count := count + 1
  logInfo m!"AUDIT COMPLETE: {count} declarations; only standard axioms"
