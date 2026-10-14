import Hindman168.NativeLatticeOrderedBasis
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

theorem native_lattice_ordered_real_basis_exists (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ b : Basis (Fin (Module.finrank ℝ E)) ℝ E,
      (∀ i, nativeLieExponential (I := I) (G := G) (b i) ∈ Γ ∧
        b i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) ∧
      Function.Bijective (nativeOrderedExponentialCoordinates (I := I) (G := G) b) ∧
      ∀ x, nativeOrderedExponentialCoordinates (I := I) (G := G) b x ∈ Γ ↔
        ∀ i, ∃ n : ℤ, x i = (n : ℝ) := by
  obtain ⟨m, hm, w, hw, hli, hbij, hlat⟩ := native_lattice_ordered_basis (I := I) Γ
  subst m
  let b := basisOfLinearIndependentOfCardEqFinrank' w hli (Fintype.card_fin _)
  have hb : (b : Fin (Module.finrank ℝ E) → E) = w :=
    coe_basisOfLinearIndependentOfCardEqFinrank' w hli (Fintype.card_fin _)
  exact ⟨b, by simpa only [hb] using hw, by simpa only [hb] using hbij,
    by simpa only [hb] using hlat⟩

noncomputable def nativeLatticeOrderedRealBasis (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] : Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  Classical.choose (native_lattice_ordered_real_basis_exists (I := I) Γ)

theorem native_lattice_ordered_real_basis_spec (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    (∀ i, nativeLieExponential (I := I) (G := G) (nativeLatticeOrderedRealBasis (I := I) Γ i) ∈ Γ ∧
      nativeLatticeOrderedRealBasis (I := I) Γ i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) ∧
    Function.Bijective (nativeOrderedExponentialCoordinates (I := I) (G := G)
      (nativeLatticeOrderedRealBasis (I := I) Γ)) ∧
    ∀ x, nativeOrderedExponentialCoordinates (I := I) (G := G)
      (nativeLatticeOrderedRealBasis (I := I) Γ) x ∈ Γ ↔ ∀ i, ∃ n : ℤ, x i = (n : ℝ) :=
  Classical.choose_spec (native_lattice_ordered_real_basis_exists (I := I) Γ)

theorem native_lattice_ordered_basis_exponential_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : Fin (Module.finrank ℝ E)) :
    nativeLieExponential (I := I) (G := G) (nativeLatticeOrderedRealBasis (I := I) Γ i) ∈ Γ :=
  ((native_lattice_ordered_real_basis_spec (I := I) Γ).1 i).1

theorem native_lattice_ordered_basis_mem_rational_span (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : Fin (Module.finrank ℝ E)) :
    nativeLatticeOrderedRealBasis (I := I) Γ i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
  ((native_lattice_ordered_real_basis_spec (I := I) Γ).1 i).2

end Hindman168
