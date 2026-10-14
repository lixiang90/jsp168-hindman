import Hindman168.IntegerSubspaceFlagBasis
import Hindman168.IntegerLatticeCoordinates

namespace Hindman168
open Module Set Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem integer_lattice_basis_layer_real_span {ι : Type*} (b : Basis ι ℤ L)
    (V : Submodule ℝ E)
    (hb : span ℤ (b '' {i | (b i : E) ∈ V}) = integerSubspaceIntersection L V)
    (hV : span ℝ ((L ⊓ V.restrictScalars ℤ : Submodule ℤ E) : Set E) = V) :
    span ℝ (b.ofZLatticeBasis ℝ L '' {i | b.ofZLatticeBasis ℝ L i ∈ V}) = V := by
  have he : b.ofZLatticeBasis ℝ L '' {i | b.ofZLatticeBasis ℝ L i ∈ V} =
      L.subtype '' (b '' {i | (b i : E) ∈ V}) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨b i, ⟨i, by simpa only [Basis.ofZLatticeBasis_apply] using hi, rfl⟩,
        (Basis.ofZLatticeBasis_apply ℝ L b i).symm⟩
    · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, by simpa only [Basis.ofZLatticeBasis_apply] using hi,
        Basis.ofZLatticeBasis_apply ℝ L b i⟩
  rw [he, ← span_span_of_tower (R := ℤ) (S := ℝ), ← Submodule.map_span, hb]
  change span ℝ (((V.restrictScalars ℤ).comap L.subtype).map L.subtype : Set E) = V
  rw [Submodule.map_comap_subtype]
  exact hV

theorem integer_lattice_flag_basis_exists (k : ℕ)
    (V : Fin k → Submodule ℝ E) (hV : Antitone V)
    (hspan : ∀ j, span ℝ ((L ⊓ (V j).restrictScalars ℤ : Submodule ℤ E) : Set E) = V j) :
    ∃ b : Basis (Fin (Module.finrank ℝ E)) ℤ L,
      (∀ j, span ℤ (b '' {i | (b i : E) ∈ V j}) = integerSubspaceIntersection L (V j)) ∧
      ∀ j, span ℝ (b.ofZLatticeBasis ℝ L '' {i | b.ofZLatticeBasis ℝ L i ∈ V j}) = V j := by
  letI : Module.Finite ℤ L := Module.Finite.of_basis (integerLatticeIntegerBasis L)
  obtain ⟨n, a, ha⟩ := integer_subspace_flag_basis_exists L k V hV
  have hn : n = Module.finrank ℝ E := by
    rw [← ZLattice.rank ℝ L, Module.finrank_eq_card_basis a, Fintype.card_fin]
  let b := a.reindex (finCongr hn)
  have hb : ∀ j, span ℤ (b '' {i | (b i : E) ∈ V j}) = integerSubspaceIntersection L (V j) := by
    intro j
    exact (integer_basis_adapted_reindex a (finCongr hn) (integerSubspaceIntersection L (V j))).trans
      (ha j)
  exact ⟨b, hb, fun j => integer_lattice_basis_layer_real_span L b (V j) (hb j) (hspan j)⟩

end Hindman168
