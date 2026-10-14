import Hindman168.RoughNativeConjugateLogSpan
import Hindman168.RoughNativeFixedKernel

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_conjugate_rational_subspace (Γ : Subgroup G) {v : E}
    (hv : v ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) (T : Submodule ℝ E) :
    nativeLatticeRationalSubspace (E := E) (I := I)
      (roughConjugateSubgroup Γ (nativeLieExponential (I := I) (G := G) v)) T ↔
        nativeLatticeRationalSubspace (E := E) (I := I) Γ T := by
  unfold nativeLatticeRationalSubspace
  rw [rough_native_conjugate_log_span Γ hv]

theorem rough_native_conjugate_lattice_quotient_compact (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] {v : E}
    (hv : v ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S)) :
    CompactSpace (nativeLieSubalgebraSubgroup (E := E) S ⧸
      (roughConjugateSubgroup Γ (nativeLieExponential (I := I) (G := G) v)).comap
        (nativeLieSubalgebraSubgroup (E := E) S).subtype) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I (minSmoothness ℝ 3)
  let g : G := nativeLieExponential (I := I) (G := G) v
  letI := roughConjugateSubgroup_discrete Γ g
  letI := roughConjugateSubgroup_quotient_compact Γ g
  exact nativeRationalLieLattice_quotient_compact (roughConjugateSubgroup Γ g) S
    ((rough_native_conjugate_rational_subspace Γ hv _).mpr hS)

omit [Module ℚ E] [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem rough_native_conjugate_lattice_intersection_discrete (Γ : Subgroup G)
    [DiscreteTopology Γ] (g : G) (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    DiscreteTopology ((roughConjugateSubgroup Γ g).comap
      (nativeLieSubalgebraSubgroup (E := E) S).subtype) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I (minSmoothness ℝ 3)
  letI := roughConjugateSubgroup_discrete Γ g
  exact nativeLieLattice_intersection_discrete (roughConjugateSubgroup Γ g) S

theorem rough_native_residue_kernel_quotient_compact (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S))
    (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ, ∃ r : ℚ, F x = (r : ℝ))
    (V : E) (hV : V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) (j : ℤ) :
    CompactSpace (nativeLieSubalgebraSubgroup (E := E) (nativeLieCharacterKernel S F hF) ⧸
      (roughConjugateSubgroup Γ (nativeLieExponential (I := I) (G := G) ((j : ℝ) • V))).comap
        (nativeLieSubalgebraSubgroup (E := E) (nativeLieCharacterKernel S F hF)).subtype) := by
  have hj : (j : ℝ) • V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
    simpa only [← Rat.cast_smul_eq_qsmul ℝ, Rat.cast_intCast] using
      (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ).smul_mem (j : ℚ) hV
  apply rough_native_conjugate_lattice_quotient_compact Γ hj
  rw [nativeLieCharacterKernel_model]
  exact rationalRestrictedKernel_rational _ _ F hS hQ

end Hindman168
