import Hindman168.NativeLatticeRationalForm
import Hindman168.NativeSubgroupRationalHullRoots
import Hindman168.RationalSubspaceSpanIntersection

/-! Actual rational coordinates and real-span intersections for the
ORIGINAL specified lattice. Rationality is defined using its ACTUAL
W=span_Q Log Gamma, without treating the nonabelian Log Gamma as an
additive integer lattice. No coordinate model replaces Gamma. -/

namespace Hindman168
open Module Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLatticeRealBasis_rational_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (w : nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) :
    (nativeLatticeRealBasis (E := E) (I := I) Γ).equivFun (w : E) =
      rationalCoordinateCast (Fin (Module.finrank ℝ E))
        ((nativeLatticeRationalBasis (E := E) (I := I) Γ).equivFun w) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rationalSubspaceRealBasis_coordinates _ _ _ w

 theorem nativeLattice_mem_rationalLogSpan_iff_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (v : E) :
    v ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ↔
      ∀ i, ∃ q : ℚ, (nativeLatticeRealBasis (E := E) (I := I) Γ).repr v i = (q : ℝ) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rationalSubspace_mem_iff_each_coordinate _ _ _ v

 theorem nativeLattice_exponential_positive_power_iff_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (v : E) :
    (∃ n : ℕ, 0 < n ∧ nativeLieExponential (I := I) (G := G) v ^ n ∈ Γ) ↔
      ∀ i, ∃ q : ℚ, (nativeLatticeRealBasis (E := E) (I := I) Γ).repr v i = (q : ℝ) :=
  (nativeSubgroupRationalLogSpan_mem_iff_positive_power (E := E) (I := I) Γ v).symm.trans
    (nativeLattice_mem_rationalLogSpan_iff_coordinates (E := E) (I := I) Γ v)

 theorem nativeLattice_rationalSubspace_realSpan_intersection (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (U : Submodule ℚ E)
    (hU : U ≤ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) :
    (span ℝ (U : Set E)).restrictScalars ℚ ⊓
        nativeSubgroupRationalLogSpan (E := E) (I := I) Γ = U := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  let W := nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
  let N := U.comap W.subtype
  have hm : N.map W.subtype = U :=
    (Submodule.map_comap_subtype W U).trans (inf_eq_right.mpr hU)
  have he := rationalSubspace_realSpan_intersection_eq W
    (nativeLattice_rationalLogSpan_finrank (E := E) (I := I) Γ)
    (nativeSubgroupRationalLogSpan_real_span_eq_top (E := E) (I := I) Γ) N
  rw [hm] at he
  exact he

def nativeLatticeRationalSubspace (Γ : Subgroup G) (V : Submodule ℝ E) : Prop :=
  span ℝ ((V.restrictScalars ℚ ⊓ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ : Submodule ℚ E) : Set E) = V

 theorem nativeLatticeRationalSubspace_realSpan (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (U : Submodule ℚ E)
    (hU : U ≤ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) :
    nativeLatticeRationalSubspace (E := E) (I := I) Γ (span ℝ (U : Set E)) := by
  unfold nativeLatticeRationalSubspace
  rw [nativeLattice_rationalSubspace_realSpan_intersection (E := E) (I := I) Γ U hU]

end Hindman168
