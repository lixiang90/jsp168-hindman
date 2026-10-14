import Hindman168.NativeLatticeRationalCoordinates
import Hindman168.NativeSubgroupRealLieSpan
import Hindman168.RationalSubspaceDimensions

/-! For an actual native Lie subalgebra S, the Q-log span of the
ACTUAL intersection Gamma intersect Exp(S) is exactly W_Gamma intersect S.
Full positive-root membership proves the difficult inclusion in the SAME
original group. If S is Gamma-rational, these intersection logarithms
therefore real-span S. No cocompactness or additive Log Gamma is assumed. -/

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeSubgroupRationalLogSpan_inf_lieSubalgebra (Γ : Subgroup G)
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    nativeSubgroupRationalLogSpan (E := E) (I := I)
        (Γ ⊓ nativeLieSubalgebraSubgroup (E := E) S) =
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ⊓
        (nativeLieSubalgebraModel (E := E) S).restrictScalars ℚ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨g, hg, rfl⟩
    exact ⟨nativeSubgroup_logarithm_mem_span Γ hg.1,
      (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff (E := E) S g).mp hg.2⟩
  · intro v hv
    obtain ⟨n, hn, hp⟩ :=
      (nativeSubgroupRationalLogSpan_mem_iff_positive_power (E := E) (I := I) Γ v).mp hv.1
    apply (nativeSubgroupRationalLogSpan_mem_iff_positive_power (E := E) (I := I)
      (Γ ⊓ nativeLieSubalgebraSubgroup (E := E) S) v).mpr
    exact ⟨n, hn, hp, (nativeLieSubalgebraSubgroup (E := E) S).pow_mem ⟨v, hv.2, rfl⟩ n⟩

 theorem nativeSubgroupRationalHull_inf_lieSubalgebra (Γ : Subgroup G)
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    nativeSubgroupRationalHull (E := E) (I := I)
        (Γ ⊓ nativeLieSubalgebraSubgroup (E := E) S) =
      nativeSubgroupRationalHull (E := E) (I := I) Γ ⊓
        nativeLieSubalgebraSubgroup (E := E) S := by
  ext g
  rw [nativeSubgroupRationalHull_mem_iff,
    nativeSubgroupRationalLogSpan_inf_lieSubalgebra]
  change nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ∧
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
        nativeLieSubalgebraModel (E := E) S ↔
    g ∈ nativeSubgroupRationalHull (E := E) (I := I) Γ ∧
      g ∈ nativeLieSubalgebraSubgroup (E := E) S
  exact and_congr (nativeSubgroupRationalHull_mem_iff (E := E) (I := I) Γ g).symm
    (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff (E := E) S g).symm

 theorem nativeRationalLieSubalgebra_intersection_logarithms_real_span (Γ : Subgroup G)
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ
      (nativeLieSubalgebraModel (E := E) S)) :
    span ℝ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) ''
      ((Γ ⊓ nativeLieSubalgebraSubgroup (E := E) S : Subgroup G) : Set G)) =
        nativeLieSubalgebraModel (E := E) S := by
  rw [← nativeSubgroupRationalLogSpan_real_span_eq,
    nativeSubgroupRationalLogSpan_inf_lieSubalgebra, inf_comm]
  exact hS

 theorem nativeRationalLieSubalgebra_intersection_realLieSpan_eq (Γ : Subgroup G)
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ
      (nativeLieSubalgebraModel (E := E) S)) :
    nativeSubgroupRealLieSpan (E := E) (I := I)
      (Γ ⊓ nativeLieSubalgebraSubgroup (E := E) S) = S := by
  ext v
  change v ∈ span ℝ
    (nativeSubgroupRationalLogSpan (E := E) (I := I)
      (Γ ⊓ nativeLieSubalgebraSubgroup (E := E) S) : Set E) ↔
        v ∈ nativeLieSubalgebraModel (E := E) S
  rw [nativeSubgroupRationalLogSpan_inf_lieSubalgebra, inf_comm]
  rw [hS]

 theorem nativeRationalLieSubalgebra_intersection_expRealLieSpan_eq (Γ : Subgroup G)
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ
      (nativeLieSubalgebraModel (E := E) S)) :
    nativeLieSubalgebraSubgroup (E := E)
      (nativeSubgroupRealLieSpan (E := E) (I := I)
        (Γ ⊓ nativeLieSubalgebraSubgroup (E := E) S)) =
          nativeLieSubalgebraSubgroup (E := E) S := by
  rw [nativeRationalLieSubalgebra_intersection_realLieSpan_eq Γ S hS]

 theorem nativeLattice_lieSubalgebra_intersection_rationalLogSpan_finiteDimensional
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    FiniteDimensional ℚ (nativeSubgroupRationalLogSpan (E := E) (I := I)
      (Γ ⊓ nativeLieSubalgebraSubgroup (E := E) S)) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  have hle : nativeSubgroupRationalLogSpan (E := E) (I := I)
      (Γ ⊓ nativeLieSubalgebraSubgroup (E := E) S) ≤
        nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
    rw [nativeSubgroupRationalLogSpan_inf_lieSubalgebra]
    exact inf_le_left
  exact Submodule.finiteDimensional_of_le hle

 theorem nativeLattice_rationalLieSubalgebra_intersection_rationalLogSpan_finrank
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ
      (nativeLieSubalgebraModel (E := E) S)) :
    Module.finrank ℚ (nativeSubgroupRationalLogSpan (E := E) (I := I)
      (Γ ⊓ nativeLieSubalgebraSubgroup (E := E) S)) =
        Module.finrank ℝ (nativeLieSubalgebraModel (E := E) S) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  let U := nativeSubgroupRationalLogSpan (E := E) (I := I)
      (Γ ⊓ nativeLieSubalgebraSubgroup (E := E) S)
  have hle : U ≤ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
    dsimp only [U]
    rw [nativeSubgroupRationalLogSpan_inf_lieSubalgebra]
    exact inf_le_left
  have he := rationalSubspace_subspace_realSpan_finrank
    (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)
    (nativeLattice_rationalLogSpan_finrank (E := E) (I := I) Γ)
    (nativeSubgroupRationalLogSpan_real_span_eq_top (E := E) (I := I) Γ) U hle
  have hs : span ℝ (U : Set E) = nativeLieSubalgebraModel (E := E) S := by
    rw [nativeSubgroupRationalLogSpan_real_span_eq]
    exact nativeRationalLieSubalgebra_intersection_logarithms_real_span Γ S hS
  rw [hs] at he
  exact he.symm

 theorem nativeRationalLieSubalgebra_exists_actual_lattice_pivot (Γ : Subgroup G)
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ
      (nativeLieSubalgebraModel (E := E) S))
    (f : E →ₗ[ℝ] ℝ) {v : E} (hv : v ∈ nativeLieSubalgebraModel (E := E) S)
    (hfv : f v ≠ 0) :
    ∃ γ : G, γ ∈ Γ ∧ γ ∈ nativeLieSubalgebraSubgroup (E := E) S ∧
      f (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hle : span ℝ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) ''
      ((Γ ⊓ nativeLieSubalgebraSubgroup (E := E) S : Subgroup G) : Set G)) ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro w ⟨γ, hγ, rfl⟩
    exact hn γ hγ.1 hγ.2
  rw [nativeRationalLieSubalgebra_intersection_logarithms_real_span Γ S hS] at hle
  exact hfv (hle hv)

end Hindman168
