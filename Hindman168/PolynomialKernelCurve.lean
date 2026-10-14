import Hindman168.PolynomialKernelBasis
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The paper's finite polynomial kernel curve

Index the off-anchor columns by Fin m in an (m+1)-column row. Responses
have degree at most m-1 and a nonzero coefficient for every nonparallel row.
A degree-B nonzero polynomial cannot vanish at all B+1 positive integers.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def kernelResponsePolynomial {R : Type*} [CommRing R] {m : ℕ}
    (A B : Fin (m + 1) → R) (j : Fin (m + 1)) : Polynomial R :=
  ∑ k : Fin m, Polynomial.monomial k.val (polynomialRowMinor A B j (j.succAbove k))

theorem kernelResponsePolynomial_coeff {R : Type*} [CommRing R] {m : ℕ}
    (A B : Fin (m + 1) → R) (j : Fin (m + 1)) (k : Fin m) :
    (kernelResponsePolynomial A B j).coeff k.val = polynomialRowMinor A B j (j.succAbove k) := by
  simp [kernelResponsePolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Fin.val_inj]

theorem kernelResponsePolynomial_ne_zero {R : Type*} [CommRing R] [IsDomain R] {m : ℕ}
    (A B : Fin (m + 1) → R) (j : Fin (m + 1)) (hj : A j ≠ 0)
    (hpair : ∃ k l, polynomialRowMinor A B k l ≠ 0) : kernelResponsePolynomial A B j ≠ 0 := by
  obtain ⟨k, hk⟩ := polynomialRowMinor_off_anchor_exists A B j hj hpair
  intro hz
  have he := kernelResponsePolynomial_coeff A B j k
  rw [hz, Polynomial.coeff_zero] at he
  exact hk he.symm

theorem kernelResponsePolynomial_natDegree_le {R : Type*} [CommRing R] {m : ℕ}
    (A B : Fin (m + 1) → R) (j : Fin (m + 1)) :
    (kernelResponsePolynomial A B j).natDegree ≤ m - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

noncomputable def polynomialKernelCurve {R : Type*} [CommRing R] {m : ℕ}
    (A : Fin (m + 1) → R) (j : Fin (m + 1)) (t : ℕ) : Fin (m + 1) → R :=
  fun c => ∑ k : Fin m, (t : R) ^ k.val * polynomialKernelBasis A j (j.succAbove k) c

theorem polynomialKernelCurve_response {R : Type*} [CommRing R] {m : ℕ}
    (A B : Fin (m + 1) → R) (j : Fin (m + 1)) (t : ℕ) :
    polynomialRowResponse B (polynomialKernelCurve A j t) =
      (kernelResponsePolynomial A B j).eval (t : R) := by
  unfold polynomialRowResponse polynomialKernelCurve kernelResponsePolynomial
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = (t : R) ^ k.val * polynomialRowResponse B (polynomialKernelBasis A j (j.succAbove k)) := by
      unfold polynomialRowResponse
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by rw [polynomialKernelBasis_response]; ring

theorem polynomialKernelCurve_annihilates {R : Type*} [CommRing R] {m : ℕ}
    (A : Fin (m + 1) → R) (j : Fin (m + 1)) (t : ℕ) :
    polynomialRowResponse A (polynomialKernelCurve A j t) = 0 := by
  rw [polynomialKernelCurve_response]
  have hz : kernelResponsePolynomial A A j = 0 := by
    have hm (k : Fin m) : polynomialRowMinor A A j (j.succAbove k) = 0 := by
      unfold polynomialRowMinor
      ring
    simp only [kernelResponsePolynomial]
    simp_rw [hm]
    simp
  rw [hz, Polynomial.eval_zero]

theorem polynomial_exists_positive_bounded_eval_ne_zero {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R] (P : Polynomial R) (hP : P ≠ 0)
    (B : ℕ) (hB : P.natDegree ≤ B) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ B + 1 ∧ P.eval (t : R) ≠ 0 := by
  have hi : Function.Injective (fun k : Fin (B + 1) => (k.val + 1 : R)) := by
    intro i j he
    change (i.val : R) + 1 = (j.val : R) + 1 at he
    apply Fin.ext
    exact Nat.cast_injective (add_right_cancel he)
  have hex : ∃ k : Fin (B + 1), P.eval (k.val + 1 : R) ≠ 0 := by
    by_contra! hz
    exact hP (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hi hz
      (by simpa using Nat.lt_succ_of_le hB))
  obtain ⟨k, hk⟩ := hex
  refine ⟨k.val + 1, by omega, by omega, ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one] using hk

end Hindman168
