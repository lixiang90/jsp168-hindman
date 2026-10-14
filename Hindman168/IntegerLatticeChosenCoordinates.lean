import Hindman168.IntegerLatticeCoordinates

namespace Hindman168
open Module
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)

omit [Fintype ι] in
theorem integer_lattice_chosen_basis_column_mem (i : ι) : b.ofZLatticeBasis ℝ L i ∈ L := by
  rw [Basis.ofZLatticeBasis_apply]
  exact (b i).property

omit [Fintype ι] in
theorem integer_lattice_chosen_basis_coordinates_of_mem (v : L) (i : ι) :
    (b.ofZLatticeBasis ℝ L).repr (v : E) i = (b.repr v i : ℝ) :=
  Basis.ofZLatticeBasis_repr_apply ℝ L b v i

theorem integer_lattice_chosen_basis_mem_iff_coordinates (v : E) :
    v ∈ L ↔ ∀ i, ∃ n : ℤ, (b.ofZLatticeBasis ℝ L).repr v i = (n : ℝ) := by
  constructor
  · intro hv i
    exact ⟨b.repr ⟨v, hv⟩ i, integer_lattice_chosen_basis_coordinates_of_mem L b ⟨v, hv⟩ i⟩
  · intro hv
    choose n hn using hv
    have he : v = ∑ i, (n i : ℝ) • b.ofZLatticeBasis ℝ L i := by
      rw [← (b.ofZLatticeBasis ℝ L).sum_repr v]
      simp only [hn]
    rw [he]
    apply L.sum_mem
    intro i _
    simpa only [Int.cast_smul_eq_zsmul] using
      L.smul_mem (n i) (integer_lattice_chosen_basis_column_mem L b i)

theorem integer_lattice_chosen_basis_synthesis_mem_iff (x : ι → ℝ) :
    (b.ofZLatticeBasis ℝ L).equivFun.symm x ∈ L ↔ ∀ i, ∃ n : ℤ, x i = (n : ℝ) := by
  rw [integer_lattice_chosen_basis_mem_iff_coordinates L b]
  change (∀ i, ∃ n : ℤ, ((b.ofZLatticeBasis ℝ L).equivFun
    ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) i = (n : ℝ)) ↔ _
  rw [LinearEquiv.apply_symm_apply]

end Hindman168
