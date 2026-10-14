import Hindman168.RoughBoxCharacterFixedSupport
import Mathlib.RingTheory.Polynomial.Pochhammer

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

noncomputable def roughMvFallingPolynomial {κ R : Type*} [Fintype κ] [CommRing R]
    (J : κ → ℕ) : MvPolynomial κ R :=
  ∏ j, ∏ k ∈ Finset.range (J j), (X j-C (k : R))

noncomputable def roughMvBinomialPolynomial {κ : Type*} [Fintype κ]
    (J : κ → ℕ) : MvPolynomial κ ℝ :=
  (∏ j, C ((J j).factorial : ℝ)⁻¹)*roughMvFallingPolynomial J

noncomputable def roughMvClearedBinomialPolynomial {κ : Type*} [Fintype κ]
    (q : ℕ) (J : κ → ℕ) : MvPolynomial κ ℤ :=
  (∏ j, C ((q.factorial/(J j).factorial : ℕ) : ℤ))*roughMvFallingPolynomial J

theorem rough_mv_falling_map {κ R T : Type*} [Fintype κ]
    [CommRing R] [CommRing T] (f : R →+* T) (J : κ → ℕ) :
    map f (roughMvFallingPolynomial J) = roughMvFallingPolynomial J := by
  simp [roughMvFallingPolynomial]

theorem rough_mv_binomial_denominator {κ : Type*} [Fintype κ]
    (q : ℕ) (J : κ → ℕ) (hJ : ∀ j, J j ≤ q) :
    C ((q.factorial : ℝ)^(Fintype.card κ))*roughMvBinomialPolynomial J =
      map (Int.castRingHom ℝ) (roughMvClearedBinomialPolynomial q J) := by
  have hdiv : ∀ j, ((q.factorial/(J j).factorial : ℕ) : ℝ) =
      (q.factorial : ℝ)*((J j).factorial : ℝ)⁻¹ := fun j => by
    rw [Nat.cast_div (Nat.factorial_dvd_factorial (hJ j)) (by positivity), div_eq_mul_inv]
  simp only [roughMvClearedBinomialPolynomial, map_mul, map_prod, map_C,
    Int.coe_castRingHom, Int.cast_natCast, hdiv, rough_mv_falling_map,
    roughMvBinomialPolynomial, map_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, ← map_pow, mul_assoc]

theorem rough_mv_binomial_eval_nat {κ : Type*} [Fintype κ]
    (J v : κ → ℕ) :
    eval (fun j => (v j : ℝ)) (roughMvBinomialPolynomial J) =
      ∏ j, ((v j).choose (J j) : ℝ) := by
  simp only [roughMvBinomialPolynomial, roughMvFallingPolynomial, map_mul, map_prod,
    eval_C, map_sub, eval_X]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [Nat.cast_choose_eq_descPochhammer_div, descPochhammer_eval_eq_prod_range,
    div_eq_mul_inv]
  ring

end Hindman168
