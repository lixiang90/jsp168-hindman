import Hindman168.RoughJointCoefficientPolynomial
import Mathlib.Algebra.MvPolynomial.Equiv

namespace Hindman168
open MvPolynomial

theorem rough_option_right_monomial {κ R : Type*} [CommSemiring R]
    (m : Option κ →₀ ℕ) (r : R) :
    optionEquivRight R κ (monomial m r) =
      monomial m.some (Polynomial.monomial (m none) r) := by
  rw [optionEquivRight_apply, aeval_monomial, Finsupp.prod_option_index]
  · rw [MvPolynomial.monomial_eq, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Option.elim_none,
      Option.elim_some, map_mul, map_pow, mul_assoc]
    rw [IsScalarTower.algebraMap_apply R (Polynomial R) (MvPolynomial κ (Polynomial R))]
    rfl
  · simp
  · intros; rw [pow_add]

theorem rough_option_right_coefficient {κ R : Type*} [CommSemiring R]
    (p : MvPolynomial (Option κ) R) (I : κ →₀ ℕ) (n : ℕ) :
    Polynomial.coeff (coeff I (optionEquivRight R κ p)) n = coeff (I.optionElim n) p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial J r =>
    rw [rough_option_right_monomial]
    simp only [MvPolynomial.coeff_monomial]
    by_cases hJI : J.some = I
    · simp only [hJI, if_true]
      have he : J = I.optionElim n ↔ J none = n := by
        constructor
        · intro h
          simpa using congrArg (fun f : Option κ →₀ ℕ => f none) h
        · intro h
          rw [← Finsupp.optionElim_some J, hJI, h]
      simp only [Polynomial.coeff_monomial, he]
    · have he : J ≠ I.optionElim n := by
        intro h
        exact hJI (by rw [h]; simp)
      simp only [hJI, he, if_false, Polynomial.coeff_zero]
  | add p r hp hr =>
    simp only [map_add, coeff_add, Polynomial.coeff_add, hp, hr]

theorem rough_option_multiindex_degree {κ : Type*} (I : κ →₀ ℕ) (n : ℕ) :
    (I.optionElim n).sum (fun _ e => e) = n+I.sum (fun _ e => e) := by
  classical
  have he : I.optionElim n = I.embDomain .some+Finsupp.single none n := by
    ext x
    cases x <;> simp
  rw [he]
  simp [Finsupp.sum_add_index, Finsupp.sum_embDomain, add_comm]

theorem rough_option_right_nonzero_weighted_degree {κ R : Type*} [CommSemiring R]
    (p : MvPolynomial (Option κ) R) (I : κ →₀ ℕ)
    (hθ : coeff I (optionEquivRight R κ p) ≠ 0) :
    (coeff I (optionEquivRight R κ p)).natDegree+I.sum (fun _ e => e) ≤ p.totalDegree := by
  let θ := coeff I (optionEquivRight R κ p)
  have hn : θ.coeff θ.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hθ
  have hm : I.optionElim θ.natDegree ∈ p.support := by
    rw [mem_support_iff, ← rough_option_right_coefficient]
    exact hn
  rw [← rough_option_multiindex_degree]
  exact le_totalDegree hm

theorem rough_option_right_weighted_degree {κ R : Type*} [CommSemiring R]
    (p : MvPolynomial (Option κ) R) (I : κ →₀ ℕ) (q : ℕ)
    (hp : p.totalDegree ≤ q) (hI : I.sum (fun _ e => e) ≤ q) :
    (coeff I (optionEquivRight R κ p)).natDegree+I.sum (fun _ e => e) ≤ q := by
  by_cases hθ : coeff I (optionEquivRight R κ p) = 0
  · simpa only [hθ, Polynomial.natDegree_zero, zero_add] using hI
  · exact (rough_option_right_nonzero_weighted_degree p I hθ).trans hp

end Hindman168
