import Hindman168.NativeLatticeFilteredSmoothBasis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Hindman168
open Module
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_lattice_filtered_smooth_real_basis_exists (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ b : Basis (Fin (Module.finrank ℝ E)) ℝ E,
      (∀ i, nativeLieExponential (I := I) (G := G) (b i) ∈ Γ ∧
        b i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) ∧
      Function.Bijective (nativeOrderedExponentialCoordinates (I := I) (G := G) b) ∧
      (∀ x, nativeOrderedExponentialCoordinates (I := I) (G := G) b x ∈ Γ ↔
        ∀ i, ∃ n : ℤ, x i = (n : ℝ)) ∧
      NativeOrderedCoordinateSmoothInverse (I := I) (G := G) b ∧
      ∃ t : ℕ → ℕ, ∀ k,
        t k ≤ Module.finrank ℝ E ∧
        (∀ i, b i ∈ nativeLieLowerCentralModel (I := I) (G := G) k ↔ t k ≤ i.val) ∧
        Submodule.span ℝ (b '' {i | t k ≤ i.val}) = nativeLieLowerCentralModel (I := I) (G := G) k := by
  obtain ⟨m, hm, w, hw, hli, hbij, hlat, hinv, t, ht⟩ := native_lattice_filtered_smooth_basis (I := I) Γ
  subst m
  let b := basisOfLinearIndependentOfCardEqFinrank' w hli (Fintype.card_fin _)
  have hb : (b : Fin (Module.finrank ℝ E) → E) = w :=
    coe_basisOfLinearIndependentOfCardEqFinrank' w hli (Fintype.card_fin _)
  refine ⟨b, by simpa only [hb] using hw, by simpa only [hb] using hbij,
    by simpa only [hb] using hlat, by simpa only [hb] using hinv, t, ?_⟩
  simpa only [hb] using ht

noncomputable def nativeLatticeFilteredSmoothRealBasis (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] : Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  Classical.choose (native_lattice_filtered_smooth_real_basis_exists (I := I) Γ)

theorem native_lattice_filtered_smooth_real_basis_spec (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    (∀ i, nativeLieExponential (I := I) (G := G) (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i) ∈ Γ ∧
      nativeLatticeFilteredSmoothRealBasis (I := I) Γ i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) ∧
    Function.Bijective (nativeOrderedExponentialCoordinates (I := I) (G := G)
      (nativeLatticeFilteredSmoothRealBasis (I := I) Γ)) ∧
    (∀ x, nativeOrderedExponentialCoordinates (I := I) (G := G)
      (nativeLatticeFilteredSmoothRealBasis (I := I) Γ) x ∈ Γ ↔ ∀ i, ∃ n : ℤ, x i = (n : ℝ)) ∧
    NativeOrderedCoordinateSmoothInverse (I := I) (G := G) (nativeLatticeFilteredSmoothRealBasis (I := I) Γ) ∧
    ∃ t : ℕ → ℕ, ∀ k,
      t k ≤ Module.finrank ℝ E ∧
      (∀ i, nativeLatticeFilteredSmoothRealBasis (I := I) Γ i ∈
        nativeLieLowerCentralModel (I := I) (G := G) k ↔ t k ≤ i.val) ∧
      Submodule.span ℝ (nativeLatticeFilteredSmoothRealBasis (I := I) Γ '' {i | t k ≤ i.val}) =
        nativeLieLowerCentralModel (I := I) (G := G) k :=
  Classical.choose_spec (native_lattice_filtered_smooth_real_basis_exists (I := I) Γ)

noncomputable def nativeLatticeFilteredLayerStart (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] : ℕ → ℕ :=
  Classical.choose (native_lattice_filtered_smooth_real_basis_spec (I := I) Γ).2.2.2.2

theorem native_lattice_filtered_layer_start_spec (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (k : ℕ) :
    nativeLatticeFilteredLayerStart (I := I) Γ k ≤ Module.finrank ℝ E ∧
      (∀ i, nativeLatticeFilteredSmoothRealBasis (I := I) Γ i ∈
        nativeLieLowerCentralModel (I := I) (G := G) k ↔
          nativeLatticeFilteredLayerStart (I := I) Γ k ≤ i.val) ∧
      Submodule.span ℝ (nativeLatticeFilteredSmoothRealBasis (I := I) Γ ''
        {i | nativeLatticeFilteredLayerStart (I := I) Γ k ≤ i.val}) =
          nativeLieLowerCentralModel (I := I) (G := G) k :=
  Classical.choose_spec (native_lattice_filtered_smooth_real_basis_spec (I := I) Γ).2.2.2.2 k

theorem native_lattice_filtered_smooth_basis_exponential_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : Fin (Module.finrank ℝ E)) :
    nativeLieExponential (I := I) (G := G) (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i) ∈ Γ :=
  ((native_lattice_filtered_smooth_real_basis_spec (I := I) Γ).1 i).1

theorem native_lattice_filtered_smooth_basis_mem_rational_span (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : Fin (Module.finrank ℝ E)) :
    nativeLatticeFilteredSmoothRealBasis (I := I) Γ i ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
  ((native_lattice_filtered_smooth_real_basis_spec (I := I) Γ).1 i).2

noncomputable def nativeLatticeFilteredDiffeomorph (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Diffeomorph 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) I (Fin (Module.finrank ℝ E) → ℝ) G ∞ where
  toEquiv :=
    { toFun := nativeOrderedExponentialCoordinates (I := I) (G := G)
        (nativeLatticeFilteredSmoothRealBasis (I := I) Γ)
      invFun := Classical.choose (native_lattice_filtered_smooth_real_basis_spec (I := I) Γ).2.2.2.1
      left_inv := (Classical.choose_spec (native_lattice_filtered_smooth_real_basis_spec (I := I) Γ).2.2.2.1).1
      right_inv := (Classical.choose_spec (native_lattice_filtered_smooth_real_basis_spec (I := I) Γ).2.2.2.1).2.1 }
  contMDiff_toFun := native_ordered_exponential_coordinates_contMDiff (I := I) (G := G) _
  contMDiff_invFun := (Classical.choose_spec (native_lattice_filtered_smooth_real_basis_spec (I := I) Γ).2.2.2.1).2.2

theorem native_lattice_filtered_diffeomorph_apply (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (x : Fin (Module.finrank ℝ E) → ℝ) :
    nativeLatticeFilteredDiffeomorph (I := I) Γ x =
      nativeOrderedExponentialCoordinates (I := I) (G := G) (nativeLatticeFilteredSmoothRealBasis (I := I) Γ) x := rfl

theorem native_lattice_filtered_diffeomorph_mem_iff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (x : Fin (Module.finrank ℝ E) → ℝ) :
    nativeLatticeFilteredDiffeomorph (I := I) Γ x ∈ Γ ↔ ∀ i, ∃ n : ℤ, x i = (n : ℝ) :=
  (native_lattice_filtered_smooth_real_basis_spec (I := I) Γ).2.2.1 x

end Hindman168
