import Hindman168.AffineShearAlignmentSlotFaces
import Hindman168.AffineShearAlignmentSlotLifts
import Hindman168.AlignmentDuplicatedTargetCatalogue
import Hindman168.AlignmentBinarySlotFaceSpecialization
import Hindman168.AlignmentJointShearWords
import Hindman168.AlignmentCatalogueNativeLetters
import Hindman168.AlignmentSelectedCatalogueCosets
import Hindman168.AlignmentStableCatalogueSelection
import Hindman168.AlignmentBadMassCompactness
import Hindman168.AlignmentJointRouteReadings
import Hindman168.AlignmentJointRouteReadingsCatalogue
import Hindman168.AlignmentJointRouteReadingsCover
import Hindman168.AlignmentJointRouteReadingsLift
import Hindman168.AlignmentJointRouteReadingsNative
import Hindman168.PositivePrincipalSumConditioningExposure
import Hindman168.PositivePrincipalSumConditioningOutside
import Hindman168.PositivePrincipalSumConditioningMaster
import Lean
open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let targets : List Name := [`Hindman168.AffineShearAlignmentSlotFaces, `Hindman168.AffineShearAlignmentSlotLifts, `Hindman168.AlignmentDuplicatedTargetCatalogue, `Hindman168.AlignmentBinarySlotFaceSpecialization, `Hindman168.AlignmentJointShearWords, `Hindman168.AlignmentCatalogueNativeLetters, `Hindman168.AlignmentSelectedCatalogueCosets, `Hindman168.AlignmentStableCatalogueSelection, `Hindman168.AlignmentBadMassCompactness, `Hindman168.AlignmentJointRouteReadings, `Hindman168.AlignmentJointRouteReadingsCatalogue, `Hindman168.AlignmentJointRouteReadingsCover, `Hindman168.AlignmentJointRouteReadingsLift, `Hindman168.AlignmentJointRouteReadingsNative, `Hindman168.PositivePrincipalSumConditioningExposure, `Hindman168.PositivePrincipalSumConditioningOutside, `Hindman168.PositivePrincipalSumConditioningMaster]
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
