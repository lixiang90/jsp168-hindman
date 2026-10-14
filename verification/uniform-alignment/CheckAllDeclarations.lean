import Hindman168.SelectedAlignmentScheduleBudgets
import Hindman168.SelectedAlignmentScheduleDependence
import Hindman168.SelectedAlignmentScheduleFinal
import Hindman168.SelectedAlignmentScheduleIndexed
import Hindman168.SelectedAlignmentScheduleMass
import Hindman168.SelectedAlignmentScheduleNativeMass
import Hindman168.SelectedAlignmentSchedulePaths
import Hindman168.SelectedAlignmentSchedulePlans
import Hindman168.FinalUniformAlignment
import Hindman168.FinalStrongFromNativeInverse
import Lean
open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let targets : List Name := [`Hindman168.SelectedAlignmentScheduleBudgets, `Hindman168.SelectedAlignmentScheduleDependence, `Hindman168.SelectedAlignmentScheduleFinal, `Hindman168.SelectedAlignmentScheduleIndexed, `Hindman168.SelectedAlignmentScheduleMass, `Hindman168.SelectedAlignmentScheduleNativeMass, `Hindman168.SelectedAlignmentSchedulePaths, `Hindman168.SelectedAlignmentSchedulePlans, `Hindman168.FinalUniformAlignment, `Hindman168.FinalStrongFromNativeInverse]
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
#print Hindman168.HasUniformSelectedPrincipalAlignment
#check Hindman168.hasUniformSelectedPrincipalAlignment
#check Hindman168.strongConjecture_of_native_inverse
#print axioms Hindman168.hasUniformSelectedPrincipalAlignment
#print axioms Hindman168.strongConjecture_of_native_inverse
