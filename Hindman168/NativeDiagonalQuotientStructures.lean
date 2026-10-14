import Hindman168.NativeDiagonalCenterSubgroupEquality
import Hindman168.NativeCentralSubspaceQuotientLieGroup
import Hindman168.SubgroupQuotientStructureTransport

/-! Actual smooth manifold/group structures on ORIGINAL diagonal-center
quotient, transported along the PROVED literal subgroup equality. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal
attribute [local instance] diagonal_center_normal

@[reducible]
noncomputable def nativeDiagonalQuotientChartedSpace {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
    ChartedSpace ((D.E × D.E) ⧸ nativeDiagonalCenterModel D) ((D.G × D.G) ⧸ diagonalCenterSubgroup D.G) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
  exact subgroupQuotientChartedSpaceOfEq _ _ (native_diagonal_center_exponential_subgroup D)
    (nativeCentralSubspaceQuotientChartedSpace (I := D.I.prod D.I) (G := D.G × D.G)
      (nativeDiagonalCenterModel D) (native_diagonal_center_model_le D))

theorem native_diagonal_quotient_lieGroup {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
    letI := nativeDiagonalQuotientChartedSpace D
    LieGroup 𝓘(ℝ, (D.E × D.E) ⧸ nativeDiagonalCenterModel D) ∞
      ((D.G × D.G) ⧸ diagonalCenterSubgroup D.G) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
  let c := nativeCentralSubspaceQuotientChartedSpace (I := D.I.prod D.I) (G := D.G × D.G)
    (nativeDiagonalCenterModel D) (native_diagonal_center_model_le D)
  letI := c
  exact subgroup_quotient_lieGroup_of_eq 𝓘(ℝ, (D.E × D.E) ⧸ nativeDiagonalCenterModel D) _ _
    (native_diagonal_center_exponential_subgroup D) c
    (nativeCentralSubspaceQuotient_lieGroup (I := D.I.prod D.I) (G := D.G × D.G)
      (nativeDiagonalCenterModel D) (native_diagonal_center_model_le D))

theorem native_diagonal_quotient_simplyConnected {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    SimplyConnectedSpace ((D.G × D.G) ⧸ diagonalCenterSubgroup D.G) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
  exact subgroup_quotient_simplyConnected_of_eq _ _ (native_diagonal_center_exponential_subgroup D)
    (nativeCentralSubspaceQuotient_simplyConnected (I := D.I.prod D.I) (G := D.G × D.G)
      (nativeDiagonalCenterModel D) (native_diagonal_center_model_le D))

theorem native_diagonal_quotient_boundaryless {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
    letI := nativeDiagonalQuotientChartedSpace D
    BoundarylessManifold 𝓘(ℝ, (D.E × D.E) ⧸ nativeDiagonalCenterModel D)
      ((D.G × D.G) ⧸ diagonalCenterSubgroup D.G) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
  let c := nativeCentralSubspaceQuotientChartedSpace (I := D.I.prod D.I) (G := D.G × D.G)
    (nativeDiagonalCenterModel D) (native_diagonal_center_model_le D)
  letI := c
  letI := nativeCentralSubspaceQuotient_isManifold (I := D.I.prod D.I) (G := D.G × D.G)
    (nativeDiagonalCenterModel D) (native_diagonal_center_model_le D)
  have h : BoundarylessManifold 𝓘(ℝ, (D.E × D.E) ⧸ nativeDiagonalCenterModel D)
      ((D.G × D.G) ⧸ nativeCentralSubspaceSubgroup (I := D.I.prod D.I) (G := D.G × D.G)
        (nativeDiagonalCenterModel D) (native_diagonal_center_model_le D)) := inferInstance
  exact subgroup_quotient_boundaryless_of_eq 𝓘(ℝ, (D.E × D.E) ⧸ nativeDiagonalCenterModel D) _ _
    (native_diagonal_center_exponential_subgroup D) c h

theorem native_diagonal_quotient_t2Space {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    T2Space ((D.G × D.G) ⧸ diagonalCenterSubgroup D.G) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
  exact subgroup_quotient_t2_of_eq _ _ (native_diagonal_center_exponential_subgroup D)
    (nativeCentralSubspaceQuotient_t2Space (I := D.I.prod D.I) (G := D.G × D.G)
      (nativeDiagonalCenterModel D) (native_diagonal_center_model_le D))

end Hindman168
