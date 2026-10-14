import Hindman168.NativeLieSubalgebraIntegrationContinuity
import Hindman168.NativeLieSubalgebraLieGroup

namespace Hindman168
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {G K : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [Group K] [TopologicalSpace K] [ChartedSpace H' K]
  [LieGroup I ∞ G] [LieGroup J ∞ K] [BoundarylessManifold I G]
  [BoundarylessManifold J K] [T2Space G] [T2Space K]
  [Group.IsNilpotent G] [Group.IsNilpotent K]
  [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeLieSubalgebraIntegrate_contMDiff
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    ContMDiff 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S) J ∞
      (nativeLieSubalgebraIntegrate (E := E) (F := F) S φ) := by
  letI := nativeLieSubalgebraChartedSpace (E := E) S
  let e := nativeLieSubalgebraExponentialDiffeomorph (E := E) S
  let f := (nativeLieSubalgebraModelHom (E := E) (F := F) S φ).toContinuousLinearMap
  have h := (nativeLieExponential_contMDiff (I := J) (G := K)).comp
    (f.contDiff.contMDiff.comp e.contMDiff_invFun)
  exact h.congr (fun g => nativeLieSubalgebraIntegrate_formula S φ g)

end Hindman168

