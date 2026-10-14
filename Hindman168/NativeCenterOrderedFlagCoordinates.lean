import Hindman168.NativeCenterOrderedFlagBasis
import Hindman168.IntegerLatticeChosenCoordinates
import Hindman168.BasisLayerCoordinates
import Hindman168.OrderedFlagDimensions

namespace Hindman168
open Module Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCenterOrderedFlagIntegerBasis (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Basis (Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) ℤ
      (nativeCenterLogLattice (I := I) Γ) :=
  (native_center_ordered_flag_integer_basis_exists (E := E) (I := I) Γ).choose

noncomputable def nativeCenterOrderedFlagStart (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] : ℕ → ℕ :=
  (native_center_ordered_flag_integer_basis_exists (E := E) (I := I) Γ).choose_spec.choose

theorem native_center_ordered_flag_integer_spec (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ) :
    nativeCenterOrderedFlagStart (I := I) Γ j ≤ Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)) ∧
      (∀ i, ((nativeCenterOrderedFlagIntegerBasis (I := I) Γ i).val.val : E) ∈
        nativeLieLowerCentralModel (I := I) (G := G) j ↔ nativeCenterOrderedFlagStart (I := I) Γ j ≤ i.val) ∧
      span ℤ (nativeCenterOrderedFlagIntegerBasis (I := I) Γ ''
        {i | nativeCenterOrderedFlagStart (I := I) Γ j ≤ i.val}) =
          nativeCenterLayerIntegerIntersection (I := I) Γ j :=
  (native_center_ordered_flag_integer_basis_exists (E := E) (I := I) Γ).choose_spec.choose_spec j

noncomputable def nativeCenterOrderedFlagRealBasis (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Basis (Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) ℝ
      (nativeLieCenterModel (I := I) (G := G)) := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  exact (nativeCenterOrderedFlagIntegerBasis (I := I) Γ).ofZLatticeBasis ℝ _

theorem native_center_ordered_flag_real_basis_apply (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (i : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) :
    nativeCenterOrderedFlagRealBasis (I := I) Γ i =
      (nativeCenterOrderedFlagIntegerBasis (I := I) Γ i).val := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  exact Basis.ofZLatticeBasis_apply ℝ _ _ i

theorem native_center_ordered_flag_real_suffix_span (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ) :
    span ℝ (nativeCenterOrderedFlagRealBasis (I := I) Γ ''
      {i | nativeCenterOrderedFlagStart (I := I) Γ j ≤ i.val}) =
        (nativeLieLowerCentralModel (I := I) (G := G) j).comap
          (nativeLieCenterModel (I := I) (G := G)).subtype := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  let b := nativeCenterOrderedFlagIntegerBasis (I := I) Γ
  let C := nativeLieCenterModel (I := I) (G := G)
  let L := nativeCenterLogLattice (I := I) Γ
  let V := (nativeLieLowerCentralModel (I := I) (G := G) j).comap C.subtype
  have hm : {i | (b i : C) ∈ V} = {i | nativeCenterOrderedFlagStart (I := I) Γ j ≤ i.val} :=
    Set.ext (fun i => (native_center_ordered_flag_integer_spec Γ j).2.1 i)
  have hb : span ℤ (b '' {i | (b i : C) ∈ V}) = integerSubspaceIntersection L V := by
    rw [hm]
    exact (native_center_ordered_flag_integer_spec Γ j).2.2
  have hr := integer_lattice_basis_layer_real_span L b V hb (native_center_layer_integer_real_span Γ j)
  have he : {i | b.ofZLatticeBasis ℝ L i ∈ V} = {i | nativeCenterOrderedFlagStart (I := I) Γ j ≤ i.val} := by
    simp only [Basis.ofZLatticeBasis_apply]
    exact hm
  rw [he] at hr
  exact hr

theorem native_center_ordered_flag_exponential_mem_iff_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (v : nativeLieCenterModel (I := I) (G := G)) :
    nativeLieExponential (I := I) (G := G) v.val ∈ Γ ↔
      ∀ i, ∃ n : ℤ, (nativeCenterOrderedFlagRealBasis (I := I) Γ).repr v i = (n : ℝ) := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  exact integer_lattice_chosen_basis_mem_iff_coordinates
    (nativeCenterLogLattice (I := I) Γ) (nativeCenterOrderedFlagIntegerBasis (I := I) Γ) v

theorem native_center_ordered_flag_layer_mem_iff_prefix_zero (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ)
    (v : nativeLieCenterModel (I := I) (G := G)) :
    v.val ∈ nativeLieLowerCentralModel (I := I) (G := G) j ↔
      ∀ i, i.val < nativeCenterOrderedFlagStart (I := I) Γ j →
        (nativeCenterOrderedFlagRealBasis (I := I) Γ).repr v i = 0 := by
  have h := basis_layer_mem_iff_zero_coordinates (nativeCenterOrderedFlagRealBasis (I := I) Γ)
    (fun i => nativeCenterOrderedFlagStart (I := I) Γ j ≤ i.val) _
    (native_center_ordered_flag_real_suffix_span Γ j) v
  simpa only [not_le, Submodule.mem_comap, Submodule.subtype_apply] using h

theorem native_center_ordered_flag_start_monotone (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Monotone (nativeCenterOrderedFlagStart (I := I) Γ) := by
  intro j k hjk
  let n := Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))
  let t := nativeCenterOrderedFlagStart (I := I) Γ
  by_cases hk : t k < n
  · let i : Fin n := ⟨t k, hk⟩
    have hm := (native_center_ordered_flag_integer_spec Γ k).2.1 i |>.mpr le_rfl
    have hj := nativeLieLowerCentralModel_antitone (I := I) (G := G) hjk hm
    exact (native_center_ordered_flag_integer_spec Γ j).2.1 i |>.mp hj
  · have hk' : n ≤ t k := Nat.le_of_not_gt hk
    exact (native_center_ordered_flag_integer_spec Γ j).1.trans hk'

theorem native_center_ordered_flag_start_eq_codimension (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ) :
    nativeCenterOrderedFlagStart (I := I) Γ j =
      Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)) -
        Module.finrank ℝ ((nativeLieLowerCentralModel (I := I) (G := G) j).comap
          (nativeLieCenterModel (I := I) (G := G)).subtype) := by
  have h := basis_suffix_span_finrank (nativeCenterOrderedFlagRealBasis (I := I) Γ)
    (nativeCenterOrderedFlagStart (I := I) Γ j)
  rw [native_center_ordered_flag_real_suffix_span Γ j] at h
  have ht := (native_center_ordered_flag_integer_spec (E := E) (I := I) Γ j).1
  omega

end Hindman168
