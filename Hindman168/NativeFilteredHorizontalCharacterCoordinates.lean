import Hindman168.NativeFilteredHorizontalLatticeImage

namespace Hindman168
open Module
open scoped Classical BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_filtered_horizontal_indices_card (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    (nativeFilteredHorizontalIndices (I := I) Γ).card = nativeLatticeFilteredLayerStart (I := I) Γ 1 := by
  let n := Module.finrank ℝ E
  let t := nativeLatticeFilteredLayerStart (I := I) Γ 1
  have ht : t ≤ n := (native_lattice_filtered_layer_start_spec (I := I) Γ 1).1
  by_cases hlt : t < n
  · have he : nativeFilteredHorizontalIndices (I := I) Γ = Finset.Iio (⟨t, hlt⟩ : Fin n) := by
      ext i
      simp only [nativeFilteredHorizontalIndices, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_Iio, Fin.lt_def, t]
    rw [he, Fin.card_Iio]
  · have heq : t = n := le_antisymm ht (Nat.le_of_not_gt hlt)
    have he : nativeFilteredHorizontalIndices (I := I) Γ = Finset.univ := by
      ext i
      rw [native_filtered_horizontal_indices_mem_iff (I := I) Γ]
      exact ⟨fun _ => Finset.mem_univ i, fun _ => lt_of_lt_of_le i.isLt heq.ge⟩
    rw [he, Finset.card_univ, Fintype.card_fin]
    exact heq.symm

theorem native_filtered_horizontal_dimension_eq_codimension (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    (nativeFilteredHorizontalIndices (I := I) Γ).card = Module.finrank ℝ E -
      Module.finrank ℝ (nativeLieLowerCentralModel (I := I) (G := G) 1) := by
  rw [native_filtered_horizontal_indices_card (I := I) Γ,
    native_lattice_filtered_layer_start_eq_codimension (I := I) Γ]

theorem native_filtered_horizontal_character_head_evaluation (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ f.ker) (g : G) :
    nativeLieLogarithmCharacter (I := I) (G := G) f g =
      ∑ i : ↥(nativeFilteredHorizontalIndices (I := I) Γ),
        f (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i.val) *
          nativeFilteredHorizontalCoordinates (I := I) Γ g i := by
  let b := nativeLatticeFilteredSmoothRealBasis (I := I) Γ
  let v := nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g
  let S := nativeFilteredHorizontalIndices (I := I) Γ
  have hs : (∑ i : Fin (Module.finrank ℝ E), f (b i) * b.repr v i) = f v := by
    have h := congrArg f (b.sum_repr v)
    simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using h
  have hfilter : (∑ i ∈ S, f (b i) * b.repr v i) = ∑ i : Fin (Module.finrank ℝ E), f (b i) * b.repr v i := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    have htail : nativeLatticeFilteredLayerStart (I := I) Γ 1 ≤ i.val :=
      Nat.le_of_not_gt (fun h => hi ((native_filtered_horizontal_indices_mem_iff (I := I) Γ i).mpr h))
    rw [(native_filtered_horizontal_iff_tail_zero (I := I) Γ f).mp hf i htail, zero_mul]
  change f v = ∑ i : ↥S, f (b i.val) * b.repr v i.val
  exact hs.symm.trans (hfilter.symm.trans
    (Finset.sum_coe_sort S (fun i => f (b i) * b.repr v i)).symm)

theorem native_filtered_horizontal_character_integer_head_evaluation (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (a : Fin (Module.finrank ℝ E) → ℤ)
    (htail : ∀ i, nativeLatticeFilteredLayerStart (I := I) Γ 1 ≤ i.val → a i = 0) (g : G) :
    nativeLieLogarithmCharacter (I := I) (G := G)
      (nativeFilteredSmoothBasisIntegerFunctional (I := I) Γ a) g =
      ∑ i : ↥(nativeFilteredHorizontalIndices (I := I) Γ), (a i.val : ℝ) *
        nativeFilteredHorizontalCoordinates (I := I) Γ g i := by
  rw [native_filtered_horizontal_character_head_evaluation (I := I) Γ _
    ((native_filtered_integer_horizontal_iff_tail_zero (I := I) Γ a).mpr htail)]
  simp only [native_filtered_smooth_basis_integer_functional_basis]

end Hindman168
