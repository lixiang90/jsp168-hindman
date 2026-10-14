import Hindman168.NoncommutativePolynomialCalculus
import Hindman168.UnitriangularLieAlgebra
import Mathlib.RingTheory.MatrixPolynomialAlgebra

/-! Coefficient support for actual matrix-valued polynomials. The proved
matrix/polynomial ring equivalence transfers support multiplication and
uniform nilpotency from actual polynomial matrices, not from evaluations
at finitely many parameter values. -/

noncomputable section
namespace Hindman168
open Matrix Polynomial Finset

variable {n : ℕ} {R : Type*} [CommRing R]

 def MatrixPolynomialDepth (k : ℕ) (p : Polynomial (Matrix (Fin n) (Fin n) R)) : Prop :=
  ∀ d, MatrixDepth k (p.coeff d)

 theorem matrixPolynomialDepth_iff (k : ℕ) (p : Polynomial (Matrix (Fin n) (Fin n) R)) :
    MatrixPolynomialDepth k p ↔ MatrixDepth k ((matPolyEquiv (R := R)).symm p) := by
  constructor
  · intro hp i j hij
    apply Polynomial.ext
    intro d
    rw [matPolyEquiv_symm_apply_coeff, coeff_zero]
    exact hp d i j hij
  · intro hp d i j hij
    rw [← matPolyEquiv_symm_apply_coeff, hp i j hij, coeff_zero]

 theorem MatrixPolynomialDepth.mul {k l : ℕ}
    {p q : Polynomial (Matrix (Fin n) (Fin n) R)}
    (hp : MatrixPolynomialDepth k p) (hq : MatrixPolynomialDepth l q) :
    MatrixPolynomialDepth (k + l) (p * q) := by
  apply (matrixPolynomialDepth_iff _ _).mpr
  rw [map_mul]
  exact ((matrixPolynomialDepth_iff _ _).mp hp).mul ((matrixPolynomialDepth_iff _ _).mp hq)

 theorem MatrixPolynomialDepth.pow {k : ℕ}
    {p : Polynomial (Matrix (Fin n) (Fin n) R)}
    (hp : MatrixPolynomialDepth k p) (m : ℕ) : MatrixPolynomialDepth (k * m) (p ^ m) := by
  apply (matrixPolynomialDepth_iff _ _).mpr
  rw [map_pow]
  exact ((matrixPolynomialDepth_iff _ _).mp hp).pow m

 theorem MatrixPolynomialDepth.eq_zero {k : ℕ}
    {p : Polynomial (Matrix (Fin n) (Fin n) R)}
    (hp : MatrixPolynomialDepth k p) (hk : n ≤ k) : p = 0 := by
  apply Polynomial.ext
  intro d
  exact (hp d).eq_zero hk

 theorem matrixPolynomialDepth_monomial {k : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth k A) (d : ℕ) : MatrixPolynomialDepth k (monomial d A) := by
  intro r
  rw [coeff_monomial]
  split_ifs
  · exact hA
  · exact matrixDepth_zero k

 theorem matrixPolynomialDepth_nilpotent {p : Polynomial (Matrix (Fin n) (Fin n) R)}
    (hp : MatrixPolynomialDepth 1 p) : p ^ n = 0 := by
  have h : MatrixPolynomialDepth n (p ^ n) := by
    simpa only [Nat.one_mul] using hp.pow n
  exact h.eq_zero le_rfl

variable [Algebra ℚ R]
local instance polynomialMatrixAmbientLieRing : LieRing (Matrix (Fin n) (Fin n) R) :=
  LieRing.ofAssociativeRing
local instance polynomialMatrixLieRing : LieRing (Polynomial (Matrix (Fin n) (Fin n) R)) :=
  LieRing.ofAssociativeRing

 theorem polynomial_matrix_exp_conjugation_coeff_mem
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n R)
    {A B : Matrix (Fin n) (Fin n) R} (hA : A ∈ V) (hB : B ∈ V) (d r : ℕ) :
    (IsNilpotent.exp (monomial d A) * C B * IsNilpotent.exp (-(monomial d A))).coeff r ∈ V := by
  have hp := polynomialLieSubalgebra_monomial_mem V hA d
  have hq := (polynomialLieSubalgebra_C_mem_iff V B).mpr hB
  have hn : IsNilpotent (monomial d A) :=
    ⟨n, matrixPolynomialDepth_nilpotent (matrixPolynomialDepth_monomial (hV hA) d)⟩
  exact lieSubalgebra_nilpotent_exp_conjugation_mem (polynomialLieSubalgebra V) hp hn hq r

end Hindman168
