import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.LinearAlgebra.Basis.Basic

/-! A genuine full discrete integer lattice gives compatible integer,
rational and real bases. The rational basis is constructed inside the
actual rational span; its columns are the true real basis columns. -/

namespace Hindman168
open Set Submodule Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

noncomputable def integerLatticeRealBasis : Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  (Module.finBasisOfFinrankEq ℤ L (ZLattice.rank ℝ L)).ofZLatticeBasis ℝ L

 theorem integerLatticeRealBasis_integer_span :
    span ℤ (range (integerLatticeRealBasis L)) = L :=
  (Module.finBasisOfFinrankEq ℤ L (ZLattice.rank ℝ L)).ofZLatticeBasis_span ℝ

variable [Module ℚ E]

 theorem integerLatticeRealBasis_rational_span :
    span ℚ (range (integerLatticeRealBasis L)) = span ℚ (L : Set E) := by
  calc
    _ = span ℚ (span ℤ (range (integerLatticeRealBasis L)) : Set E) :=
      (span_span_of_tower (R := ℤ) (S := ℚ) (range (integerLatticeRealBasis L))).symm
    _ = _ := congrArg (fun P : Submodule ℤ E => span ℚ (P : Set E))
      (integerLatticeRealBasis_integer_span L)

noncomputable def integerLatticeRationalBasis :
    Basis (Fin (Module.finrank ℝ E)) ℚ (span ℚ (L : Set E)) :=
  Basis.map (Basis.span ((integerLatticeRealBasis L).linearIndependent.restrict_scalars' ℚ))
    (LinearEquiv.ofEq _ _ (integerLatticeRealBasis_rational_span L))

 theorem integerLatticeRationalBasis_apply (i : Fin (Module.finrank ℝ E)) :
    (integerLatticeRationalBasis L i : E) = integerLatticeRealBasis L i := by
  change (Basis.span ((integerLatticeRealBasis L).linearIndependent.restrict_scalars' ℚ) i : E) = _
  exact Basis.coe_span_apply _ _

 theorem integerLatticeRationalSpan_finiteDimensional :
    FiniteDimensional ℚ (span ℚ (L : Set E)) :=
  Module.Finite.of_basis (integerLatticeRationalBasis L)

 theorem integerLatticeRationalSpan_finrank :
    Module.finrank ℚ (span ℚ (L : Set E)) = Module.finrank ℝ E := by
  letI := integerLatticeRationalSpan_finiteDimensional L
  rw [Module.finrank_eq_card_basis (integerLatticeRationalBasis L), Fintype.card_fin]

 theorem integerLatticeRationalBasis_real_linearIndependent :
    LinearIndependent ℝ (fun i => (integerLatticeRationalBasis L i : E)) := by
  simpa only [integerLatticeRationalBasis_apply] using (integerLatticeRealBasis L).linearIndependent

end Hindman168
