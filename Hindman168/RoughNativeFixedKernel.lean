import Hindman168.RoughNativeCharacterNormalization
import Hindman168.NativeRationalLatticeCompact

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_fixed_kernel_rational_dimension (Γ : Subgroup G)
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S))
    (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ, ∃ r : ℚ, F x = (r : ℝ))
    {v : E} (hv : v ∈ nativeLieSubalgebraModel S) (hFv : F v ≠ 0) :
    nativeLatticeRationalSubspace (E := E) (I := I) Γ
      (nativeLieSubalgebraModel (nativeLieCharacterKernel S F hF)) ∧
      Module.finrank ℝ (nativeLieSubalgebraModel (nativeLieCharacterKernel S F hF)) <
        Module.finrank ℝ (nativeLieSubalgebraModel S) := by
  rw [nativeLieCharacterKernel_model]
  exact ⟨rationalRestrictedKernel_rational _ _ F hS hQ,
    restrictedKernel_finrank_lt (nativeLieSubalgebraModel S) F hv hFv⟩

theorem rough_native_fixed_kernel_quotient_compact (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S))
    (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ, ∃ r : ℚ, F x = (r : ℝ)) :
    CompactSpace (nativeLieSubalgebraSubgroup (E := E) (nativeLieCharacterKernel S F hF) ⧸
      Γ.comap (nativeLieSubalgebraSubgroup (E := E) (nativeLieCharacterKernel S F hF)).subtype) := by
  apply nativeRationalLieLattice_quotient_compact
  rw [nativeLieCharacterKernel_model]
  exact rationalRestrictedKernel_rational _ _ F hS hQ

end Hindman168
