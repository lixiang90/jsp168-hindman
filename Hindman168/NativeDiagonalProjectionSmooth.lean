import Hindman168.SubgroupQuotientProjectionTransport
import Hindman168.NativeDiagonalQuotientStructures
import Hindman168.NativeCentralSubspaceQuotientTangent

/-! ACTUAL original diagonal quotient projection is smooth and its identity
model differential is the ACTUAL original real diagonal-model quotient map. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal
attribute [local instance] diagonal_center_normal

theorem native_diagonal_projection_contMDiff {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
    letI := nativeDiagonalQuotientChartedSpace D
    ContMDiff (D.I.prod D.I) 𝓘(ℝ, (D.E × D.E) ⧸ nativeDiagonalCenterModel D) ∞
      ((↑) : D.G × D.G → (D.G × D.G) ⧸ diagonalCenterSubgroup D.G) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
  let c := nativeCentralSubspaceQuotientChartedSpace (I := D.I.prod D.I) (G := D.G × D.G)
    (nativeDiagonalCenterModel D) (native_diagonal_center_model_le D)
  letI := c
  exact subgroup_quotient_projection_contMDiff_of_eq (D.I.prod D.I)
    𝓘(ℝ, (D.E × D.E) ⧸ nativeDiagonalCenterModel D) _ _
    (native_diagonal_center_exponential_subgroup D) c
    (nativeCentralSubspaceQuotient_projection_contMDiff (I := D.I.prod D.I) (G := D.G × D.G)
      (nativeDiagonalCenterModel D) (native_diagonal_center_model_le D))

theorem native_diagonal_projection_mfderiv {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
    letI := nativeDiagonalQuotientChartedSpace D
    mfderiv (D.I.prod D.I) 𝓘(ℝ, (D.E × D.E) ⧸ nativeDiagonalCenterModel D)
      ((↑) : D.G × D.G → (D.G × D.G) ⧸ diagonalCenterSubgroup D.G) 1 =
        finiteRealQuotientProjection (nativeDiagonalCenterModel D) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
  let c := nativeCentralSubspaceQuotientChartedSpace (I := D.I.prod D.I) (G := D.G × D.G)
    (nativeDiagonalCenterModel D) (native_diagonal_center_model_le D)
  letI := c
  exact subgroup_quotient_projection_mfderiv_of_eq (D.I.prod D.I)
    𝓘(ℝ, (D.E × D.E) ⧸ nativeDiagonalCenterModel D) _ _
    (native_diagonal_center_exponential_subgroup D) c 1
    (finiteRealQuotientProjection (nativeDiagonalCenterModel D))
    (nativeCentralSubspaceQuotient_mfderiv_eq_projection (I := D.I.prod D.I) (G := D.G × D.G)
      (nativeDiagonalCenterModel D) (native_diagonal_center_model_le D))

end Hindman168
