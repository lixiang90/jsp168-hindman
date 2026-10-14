import Hindman168.IntegerLatticeRationalBasis

namespace Hindman168
open Module
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

noncomputable def integerLatticeIntegerBasis : Basis (Fin (Module.finrank ℝ E)) ℤ L :=
  Module.finBasisOfFinrankEq ℤ L (ZLattice.rank ℝ L)

theorem integer_lattice_real_basis_column_mem (i : Fin (Module.finrank ℝ E)) :
    integerLatticeRealBasis L i ∈ L := by
  rw [integerLatticeRealBasis, Basis.ofZLatticeBasis_apply]
  exact (Module.finBasisOfFinrankEq ℤ L (ZLattice.rank ℝ L) i).property

theorem integer_lattice_real_coordinates_of_mem (v : L) (i : Fin (Module.finrank ℝ E)) :
    (integerLatticeRealBasis L).repr (v : E) i =
      ((integerLatticeIntegerBasis L).repr v i : ℝ) := by
  exact Basis.ofZLatticeBasis_repr_apply ℝ L (integerLatticeIntegerBasis L) v i

theorem integer_lattice_mem_iff_integral_coordinates (v : E) :
    v ∈ L ↔ ∀ i : Fin (Module.finrank ℝ E),
      ∃ n : ℤ, (integerLatticeRealBasis L).repr v i = (n : ℝ) := by
  constructor
  · intro hv i
    exact ⟨(integerLatticeIntegerBasis L).repr ⟨v, hv⟩ i,
      integer_lattice_real_coordinates_of_mem L ⟨v, hv⟩ i⟩
  · intro hv
    choose n hn using hv
    have he : v = ∑ i, (n i : ℝ) • integerLatticeRealBasis L i := by
      rw [← (integerLatticeRealBasis L).sum_repr v]
      simp only [hn]
    rw [he]
    apply L.sum_mem
    intro i _
    simpa only [Int.cast_smul_eq_zsmul] using
      L.smul_mem (n i) (integer_lattice_real_basis_column_mem L i)

theorem integer_lattice_synthesis_mem_iff (x : Fin (Module.finrank ℝ E) → ℝ) :
    (integerLatticeRealBasis L).equivFun.symm x ∈ L ↔
      ∀ i, ∃ n : ℤ, x i = (n : ℝ) := by
  rw [integer_lattice_mem_iff_integral_coordinates]
  have he := (integerLatticeRealBasis L).equivFun.apply_symm_apply x
  change (∀ i, ∃ n : ℤ, ((integerLatticeRealBasis L).equivFun
    ((integerLatticeRealBasis L).equivFun.symm x)) i = (n : ℝ)) ↔ _
  rw [he]

end Hindman168
