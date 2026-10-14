import Hindman168.AffineShearAdaptedBasis
import Hindman168.AffineShearCosetImage
import Hindman168.AffineShearCosetNormalization
import Hindman168.AffineShearCoverLifting
import Hindman168.AffineShearCubeImage
import Hindman168.AffineShearFaceAction
import Hindman168.AffineShearFilteredSection
import Hindman168.AffineShearNativeCosetLifting
import Hindman168.AffineShearNativeGradedIdentity
import Hindman168.AffineShearNativeHomImage
import Hindman168.AffineShearNativeImageFiltration
import Hindman168.AffineShearNativeImageSection
import Hindman168.AffineShearNativeInitialLayer
import Hindman168.AffineShearNativeJointAction
import Hindman168.AffineShearNativeLift
import Hindman168.AffineShearNativeMarginalImage
import Hindman168.AffineShearNativeOrbitImage
import Hindman168.AffineShearNativeOriginalAction
import Hindman168.AffineShearNativeOriginalGraded
import Hindman168.AffineShearNativePiRestriction
import Hindman168.AffineShearNativeRestriction
import Hindman168.AffineShearWeightedSection
import Hindman168.WeightedShearWeakLimit
import Hindman168.WeightedShearNativeHaar
import Hindman168.WeightedShearJointOrbitHaar
import Hindman168.NativeFinitePiCosetRestriction
import Hindman168.NativeFinitePiRestrictedCubeProjection
import Hindman168.NativeFinitePiCubeReassembly
import Hindman168.AlignmentOriginalJointRestriction
import Hindman168.AlignmentAllTargetsCubeConditionsSelection
import Hindman168.AlignmentRestrictedRealCubeComparison
import Hindman168.AlignmentRestrictedCubeHaarInvariant
import Hindman168.AlignmentRestrictedFaceHaarInvariance
import Hindman168.AlignmentAllTargetsCommonSourceFaceHaar
import Hindman168.AlignmentSelectedAllTargetsFaceHaar
import Hindman168.AlignmentJointNativeSlotHomeomorph
import Hindman168.AlignmentRestrictedCubeSetwise
import Hindman168.AlignmentSelectedAllTargetsCosets
import Hindman168.AlignmentCubeFaceReassembly
import Hindman168.AlignmentCubeUpperFaceReassembly
import Hindman168.AlignmentJointPointMixture
import Lean
open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let targets : List Name := [`Hindman168.AffineShearAdaptedBasis, `Hindman168.AffineShearCosetImage, `Hindman168.AffineShearCosetNormalization, `Hindman168.AffineShearCoverLifting, `Hindman168.AffineShearCubeImage, `Hindman168.AffineShearFaceAction, `Hindman168.AffineShearFilteredSection, `Hindman168.AffineShearNativeCosetLifting, `Hindman168.AffineShearNativeGradedIdentity, `Hindman168.AffineShearNativeHomImage, `Hindman168.AffineShearNativeImageFiltration, `Hindman168.AffineShearNativeImageSection, `Hindman168.AffineShearNativeInitialLayer, `Hindman168.AffineShearNativeJointAction, `Hindman168.AffineShearNativeLift, `Hindman168.AffineShearNativeMarginalImage, `Hindman168.AffineShearNativeOrbitImage, `Hindman168.AffineShearNativeOriginalAction, `Hindman168.AffineShearNativeOriginalGraded, `Hindman168.AffineShearNativePiRestriction, `Hindman168.AffineShearNativeRestriction, `Hindman168.AffineShearWeightedSection, `Hindman168.WeightedShearWeakLimit, `Hindman168.WeightedShearNativeHaar, `Hindman168.WeightedShearJointOrbitHaar, `Hindman168.NativeFinitePiCosetRestriction, `Hindman168.NativeFinitePiRestrictedCubeProjection, `Hindman168.NativeFinitePiCubeReassembly, `Hindman168.AlignmentOriginalJointRestriction, `Hindman168.AlignmentAllTargetsCubeConditionsSelection, `Hindman168.AlignmentRestrictedRealCubeComparison, `Hindman168.AlignmentRestrictedCubeHaarInvariant, `Hindman168.AlignmentRestrictedFaceHaarInvariance, `Hindman168.AlignmentAllTargetsCommonSourceFaceHaar, `Hindman168.AlignmentSelectedAllTargetsFaceHaar, `Hindman168.AlignmentJointNativeSlotHomeomorph, `Hindman168.AlignmentRestrictedCubeSetwise, `Hindman168.AlignmentSelectedAllTargetsCosets, `Hindman168.AlignmentCubeFaceReassembly, `Hindman168.AlignmentCubeUpperFaceReassembly, `Hindman168.AlignmentJointPointMixture]
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
