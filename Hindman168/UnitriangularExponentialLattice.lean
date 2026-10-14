import Hindman168.UnitriangularExponentialMaps

/-! Explicit exponential coordinates for elementary matrices, and rational
coordinates for logarithms of the original integer matrix lattice. No
additive closure of that logarithm set is assumed or asserted. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]

 omit [Algebra ℚ R] in
 theorem matrixDepth_single_strict (i j : Fin n) (hij : i < j) (c : R) :
    MatrixDepth 1 (Matrix.single i j c) := by
  intro a b hab
  apply Matrix.single_apply_of_ne
  intro h
  rcases h with ⟨rfl, rfl⟩
  omega

 theorem matrixFiniteExp_single (i j : Fin n) (hij : i < j) (c : R) :
    matrixFiniteExp (Matrix.single i j c) = Matrix.transvection i j c := by
  rw [matrixFiniteExp_eq_exp (matrixDepth_single_strict i j hij c)]
  have hs : (Matrix.single i j c) ^ 2 = 0 := by
    rw [pow_two, Matrix.single_mul_single_of_ne _ _ _ _ (ne_of_lt hij).symm]
  rw [IsNilpotent.exp_eq_sum hs]
  simp [Finset.sum_range_succ, Matrix.transvection]

 theorem unitriangularLogMatrix_transvection (i j : Fin n) (hij : i < j) (c : R) :
    unitriangularLogMatrix (unitriangularTransvection i j hij c) = Matrix.single i j c := by
  apply matrixFiniteExp_injective (unitriangularLogMatrix_strict _)
    (matrixDepth_single_strict i j hij c)
  rw [matrixFiniteExp_logMatrix, matrixFiniteExp_single i j hij c]
  rfl

 omit [Algebra ℚ R] in
 theorem integer_unitriangular_rational_real (g : Unitriangular n ℤ) :
    unitriangularMap (algebraMap ℚ ℝ) (unitriangularMap (Int.castRingHom ℚ) g) =
      unitriangularMap (Int.castRingHom ℝ) g := by
  apply unitriangular_val_injective
  ext i j
  change algebraMap ℚ ℝ ((g.val : Matrix (Fin n) (Fin n) ℤ) i j : ℚ) =
    ((g.val : Matrix (Fin n) (Fin n) ℤ) i j : ℝ)
  simp

 omit [Algebra ℚ R] in
 theorem integerUnitriangularLattice_log_rational (g : Unitriangular n ℝ)
    (hg : g ∈ integerUnitriangularLattice n) :
    ∃ A : StrictUpperTriangular n ℚ,
      strictUpperTriangularMap (algebraMap ℚ ℝ) A = unitriangularLogarithm g := by
  obtain ⟨u, rfl⟩ := hg
  refine ⟨unitriangularLogarithm (unitriangularMap (Int.castRingHom ℚ) u), ?_⟩
  rw [unitriangularLogarithm_map, integer_unitriangular_rational_real]

end Hindman168
