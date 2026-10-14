import Hindman168.NilpotentLieSubalgebraConjugation
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! Actual coefficientwise polynomial Lie subalgebras, with the associative
polynomial commutator. This is the coefficient closure used by the finite
BCH differential recursion, not an assumption of BCH closure itself. -/

noncomputable section

namespace Hindman168
open Polynomial Finset

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
local instance coefficientAmbientLieRing : LieRing A := LieRing.ofAssociativeRing
local instance coefficientPolynomialLieRing : LieRing (Polynomial A) := LieRing.ofAssociativeRing

 theorem polynomial_commutator_coeff (p q : Polynomial A) (n : ℕ) :
    (p * q - q * p).coeff n =
      ∑ ij ∈ antidiagonal n, (p.coeff ij.1 * q.coeff ij.2 - q.coeff ij.2 * p.coeff ij.1) := by
  rw [coeff_sub, coeff_mul, coeff_mul, sum_sub_distrib]
  congr 1
  exact (Finset.Nat.sum_antidiagonal_swap (n := n)
    (f := fun ij => q.coeff ij.1 * p.coeff ij.2)).symm

 def polynomialLieSubalgebra (V : LieSubalgebra R A) : LieSubalgebra R (Polynomial A) where
  carrier := {p | ∀ n, p.coeff n ∈ V}
  zero_mem' n := by simpa only [coeff_zero] using V.zero_mem
  add_mem' hp hq n := by simpa only [coeff_add] using V.add_mem (hp n) (hq n)
  smul_mem' c p hp n := by simpa only [coeff_smul] using V.smul_mem c (hp n)
  lie_mem' {p q} hp hq n := by
    change (p * q - q * p).coeff n ∈ V
    rw [polynomial_commutator_coeff]
    apply V.toSubmodule.sum_mem
    intro ij _
    exact V.lie_mem (hp ij.1) (hq ij.2)

 theorem polynomialLieSubalgebra_mem_iff (V : LieSubalgebra R A) (p : Polynomial A) :
    p ∈ polynomialLieSubalgebra V ↔ ∀ n, p.coeff n ∈ V := Iff.rfl

 theorem polynomialLieSubalgebra_C_mem_iff (V : LieSubalgebra R A) (x : A) :
    C x ∈ polynomialLieSubalgebra V ↔ x ∈ V := by
  constructor
  · intro h
    simpa only [coeff_C_zero] using h 0
  · intro h n
    by_cases hn : n = 0
    · subst n; simpa only [coeff_C_zero] using h
    · simpa only [coeff_C, if_neg hn] using V.zero_mem

 theorem polynomialLieSubalgebra_monomial_mem (V : LieSubalgebra R A)
    {x : A} (hx : x ∈ V) (k : ℕ) : monomial k x ∈ polynomialLieSubalgebra V := by
  intro n
  by_cases hkn : k = n
  · simpa only [coeff_monomial, if_pos hkn] using hx
  · simpa only [coeff_monomial, if_neg hkn] using V.zero_mem

 theorem polynomialLieSubalgebra_derivative_mem (V : LieSubalgebra R A)
    {p : Polynomial A} (hp : p ∈ polynomialLieSubalgebra V) : p.derivative ∈ polynomialLieSubalgebra V := by
  intro n
  rw [coeff_derivative, ← Nat.cast_add_one, ← nsmul_eq_mul']
  exact V.toSubmodule.nsmul_mem (hp (n + 1)) (n + 1)

end Hindman168
