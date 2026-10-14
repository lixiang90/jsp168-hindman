import Hindman168.NativeFilteredSmoothBasisIntegerCharacters
import Hindman168.RoughHorizontalIntegerSize
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators

/-! A fixed finite list constructed directly from the integer coordinates
of the SAME smooth lattice basis. Exact membership and cardinality bounds
do not supply the quantitative Leibman existence theorem. -/

namespace Hindman168
open scoped Classical BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeFilteredSmoothBasisIntegerCharacterGrid (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (B : ℕ) : Finset (E →ₗ[ℝ] ℝ) :=
  ((Fintype.piFinset (fun _ : Fin (Module.finrank ℝ E) =>
      Finset.Icc (-(B : ℤ)) (B : ℤ))).image
    (nativeFilteredSmoothBasisIntegerFunctional (I := I) Γ)).filter
      (RoughNativeHorizontalFunctional (E := E) (I := I) Γ)

theorem native_filtered_smooth_basis_integer_grid_mem_iff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (B : ℕ) (f : E →ₗ[ℝ] ℝ) :
    f ∈ nativeFilteredSmoothBasisIntegerCharacterGrid (I := I) Γ B ↔
      RoughNativeHorizontalFunctional (E := E) (I := I) Γ f ∧
      ∃ a : Fin (Module.finrank ℝ E) → ℤ,
        (∀ i, -(B : ℤ) ≤ a i ∧ a i ≤ (B : ℤ)) ∧
        nativeFilteredSmoothBasisIntegerFunctional (I := I) Γ a = f := by
  simp only [nativeFilteredSmoothBasisIntegerCharacterGrid, Finset.mem_filter,
    Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc, and_comm]

theorem native_filtered_smooth_basis_integer_grid_card_le (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (B : ℕ) :
    (nativeFilteredSmoothBasisIntegerCharacterGrid (I := I) Γ B).card ≤
      (2*B+1)^(Module.finrank ℝ E) := by
  have hcard : (Finset.Icc (-(B : ℤ)) (B : ℤ)).card = 2*B+1 := by
    rw [Int.card_Icc]
    have h : (B : ℤ)+1-(-(B : ℤ)) = ((2*B+1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h, Int.toNat_natCast]
  calc
    _ ≤ ((Fintype.piFinset (fun _ : Fin (Module.finrank ℝ E) =>
        Finset.Icc (-(B : ℤ)) (B : ℤ))).image
        (nativeFilteredSmoothBasisIntegerFunctional (I := I) Γ)).card := Finset.card_filter_le _ _
    _ ≤ (Fintype.piFinset (fun _ : Fin (Module.finrank ℝ E) =>
        Finset.Icc (-(B : ℤ)) (B : ℤ))).card := Finset.card_image_le
    _ = _ := by rw [Fintype.card_piFinset_const, hcard]

theorem native_filtered_smooth_basis_integer_grid_contains (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (B : ℕ) (f : E →ₗ[ℝ] ℝ)
    (hf : RoughNativeHorizontalFunctional (E := E) (I := I) Γ f)
    (hbound : ∀ i, |f (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i)| ≤ (B : ℝ)) :
    f ∈ nativeFilteredSmoothBasisIntegerCharacterGrid (I := I) Γ B := by
  obtain ⟨a, ha, _⟩ := native_filtered_smooth_basis_horizontal_integer_representation Γ f hf
  refine (native_filtered_smooth_basis_integer_grid_mem_iff Γ B f).mpr ⟨hf, a, ?_, ha⟩
  intro i
  have h := hbound i
  rw [← ha, native_filtered_smooth_basis_integer_functional_basis, abs_le] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

theorem native_filtered_smooth_basis_integer_grid_size_contains (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (M : ℝ) (hM : 0 ≤ M)
    (a : Fin (Module.finrank ℝ E) → ℤ)
    (ha : a ≠ 0)
    (hcomm : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤
      (nativeFilteredSmoothBasisIntegerFunctional (I := I) Γ a).ker)
    (hsize : roughHorizontalIntegerSize Finset.univ a ≤ M) :
    nativeFilteredSmoothBasisIntegerFunctional (I := I) Γ a ∈
      nativeFilteredSmoothBasisIntegerCharacterGrid (I := I) Γ ⌈M⌉₊ := by
  apply native_filtered_smooth_basis_integer_grid_contains
  · exact (native_filtered_smooth_basis_integer_functional_horizontal_iff Γ a).mpr ⟨ha, hcomm⟩
  · intro i
    rw [native_filtered_smooth_basis_integer_functional_basis]
    have hs := (rough_horizontal_integer_size_le_iff Finset.univ a M hM).mp hsize
    have hi : (a i : ℝ)^2 ≤ ∑ j ∈ Finset.univ, (a j : ℝ)^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (a j : ℝ)) (Finset.mem_univ i)
    have hab : |(a i : ℝ)| ≤ M := by
      have hsq := sq_abs (a i : ℝ)
      have hn := abs_nonneg (a i : ℝ)
      nlinarith
    exact hab.trans (Nat.le_ceil M)

end Hindman168
