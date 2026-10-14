import Hindman168.FinalNativeInverseStep
import Hindman168.FinalStrongFromPrinciples
import Hindman168.FinalUniformAlignmentInput
import Hindman168.SelectedAlignmentCosetMassCover
import Hindman168.SelectedAlignmentCosetMassMixture
import Hindman168.SelectedAlignmentCosetMassPlan
import Hindman168.SelectedAlignmentCosetMassRecurrence
import Hindman168.SelectedAlignmentFailureCompactness
import Hindman168.SelectedAlignmentKeyObservableTopology
import Hindman168.SelectedAlignmentKeyReadingsLimit
import Hindman168.SelectedAlignmentKeySourceCompactness
import Hindman168.SelectedAlignmentNativeRouteFailure
import Hindman168.SelectedAlignmentNativeRouteLimit
import Hindman168.SelectedAlignmentRecipeArrayModels
import Hindman168.SelectedAlignmentRecipeRouteFailure
import Hindman168.SelectedAlignmentRouteCell
import Hindman168.SelectedAlignmentRouteNumerical
import Hindman168.SelectedAlignmentRouteNumericalPivot
import Hindman168.SelectedAlignmentRouteNumericalWords
import Hindman168.SelectedAlignmentRoutePrelimitReadings
import Hindman168.SelectedAlignmentRouteThresholdLimit
import Hindman168.SelectedAlignmentStableCatalogueSelection
import Lean
open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let targets : List Name := [`Hindman168.FinalNativeInverseStep, `Hindman168.FinalStrongFromPrinciples, `Hindman168.FinalUniformAlignmentInput, `Hindman168.SelectedAlignmentCosetMassCover, `Hindman168.SelectedAlignmentCosetMassMixture, `Hindman168.SelectedAlignmentCosetMassPlan, `Hindman168.SelectedAlignmentCosetMassRecurrence, `Hindman168.SelectedAlignmentFailureCompactness, `Hindman168.SelectedAlignmentKeyObservableTopology, `Hindman168.SelectedAlignmentKeyReadingsLimit, `Hindman168.SelectedAlignmentKeySourceCompactness, `Hindman168.SelectedAlignmentNativeRouteFailure, `Hindman168.SelectedAlignmentNativeRouteLimit, `Hindman168.SelectedAlignmentRecipeArrayModels, `Hindman168.SelectedAlignmentRecipeRouteFailure, `Hindman168.SelectedAlignmentRouteCell, `Hindman168.SelectedAlignmentRouteNumerical, `Hindman168.SelectedAlignmentRouteNumericalPivot, `Hindman168.SelectedAlignmentRouteNumericalWords, `Hindman168.SelectedAlignmentRoutePrelimitReadings, `Hindman168.SelectedAlignmentRouteThresholdLimit, `Hindman168.SelectedAlignmentStableCatalogueSelection]
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
