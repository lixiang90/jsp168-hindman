import Hindman168.SelectedAlignmentRouteKernel
import Hindman168.SelectedAlignmentRouteSecured
import Hindman168.SelectedAlignmentRouteFineGood
import Hindman168.SelectedAlignmentRouteHarmonicCoverage
import Hindman168.SelectedAlignmentRouteExtension
import Hindman168.SelectedAlignmentRouteRawKernel
import Hindman168.SelectedAlignmentRouteRawExtension
import Hindman168.SelectedAlignmentNativePivotExtension
import Hindman168.SelectedAlignmentFiniteScalePivotExtension
import Hindman168.SelectedAlignmentRouteShiftBounds
import Hindman168.SelectedAlignmentRouteCellInvariance
import Hindman168.SelectedAlignmentCompleteCell
import Lean
open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let targets : List Name := [`Hindman168.SelectedAlignmentRouteKernel, `Hindman168.SelectedAlignmentRouteSecured, `Hindman168.SelectedAlignmentRouteFineGood, `Hindman168.SelectedAlignmentRouteHarmonicCoverage, `Hindman168.SelectedAlignmentRouteExtension, `Hindman168.SelectedAlignmentRouteRawKernel, `Hindman168.SelectedAlignmentRouteRawExtension, `Hindman168.SelectedAlignmentNativePivotExtension, `Hindman168.SelectedAlignmentFiniteScalePivotExtension, `Hindman168.SelectedAlignmentRouteShiftBounds, `Hindman168.SelectedAlignmentRouteCellInvariance, `Hindman168.SelectedAlignmentCompleteCell]
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
