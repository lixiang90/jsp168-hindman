import Hindman168.LeadingCoefficientZeroBounds

/-!
# An actual decreasing-variable rough-coprimality recurrence

The complete common-prime event, including all leading-coefficient
exceptions, is bounded by two lower-dimensional common-prime probabilities
and the proved uniform error. The lower-dimensional probabilities remain
actual event masses; no desired induction hypothesis is substituted for
them in this theorem.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def dyadicCommonPrimeMass {m n : ℕ} (eF : Fin m → ℕ) (eG : Fin n → ℕ)
    (w : ℕ) (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ) : ℝ :=
  event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG)) (commonPrimeEvent w F G)

noncomputable def dyadicRecurrenceSmall {m n : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ) : ℕ :=
  1032 ^ 2 * F.degreeOf 0 * G.degreeOf 0

noncomputable def dyadicRecurrenceLarge {m n : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ) : ℕ :=
  1032 * (2 * F.totalDegree + 1) * G.degreeOf 0 +
    8 * ((∑ i, (integerPolynomialMainLeading F).degreeOf i) +
      ∑ i, (integerPolynomialMainLeading G).degreeOf i)

theorem exists_dyadic_common_prime_recurrence {m n : ℕ}
    {F : MvPolynomial (Fin (m + 1)) ℤ} {G : MvPolynomial (Fin (n + 1)) ℤ}
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ e0 : ℕ, ∀ (eF : Fin (m + 1) → ℕ) (eG : Fin (n + 1) → ℕ),
      (∀ i, e0 ≤ eF i) → (∀ i, e0 ≤ eG i) →
      (∀ i, eF i ≤ eF 0) → eF 0 ≤ eG 0 → ∀ w L : ℕ,
      0 < w → Real.exp 2 ≤ (L : ℝ) → (∀ i, L ≤ 2 ^ eF i) → (∀ i, L ≤ 2 ^ eG i) →
      dyadicCommonPrimeMass eF eG w F G ≤
        dyadicCommonPrimeMass (fun i => eF i.succ) eG w (integerPolynomialMainLeading F) G +
        dyadicCommonPrimeMass eF (fun i => eG i.succ) w F (integerPolynomialMainLeading G) +
        (dyadicRecurrenceSmall F G : ℝ) / w +
        (dyadicRecurrenceLarge F G : ℝ) * (Real.log (L : ℝ) / Real.sqrt L) := by
  obtain ⟨en, hen⟩ := exists_dyadic_prime_normalization_threshold
  obtain ⟨ez, hez⟩ := exists_dyadic_leading_zero_threshold hF hG
  obtain ⟨er, her⟩ := dyadic_regular_common_prime_uniform_endpoint F G
  let e0 := max en (max ez er)
  refine ⟨e0, ?_⟩
  intro eF eG heF heG hmax hmain w L hw hL hLF hLG
  have hHF : ∀ i, 0 < primePoolHarmonicMass (2 ^ eF i) (2 ^ (eF i + 1)) :=
    fun i => hen _ ((le_max_left _ _).trans (heF i))
  have hHG : ∀ i, 0 < primePoolHarmonicMass (2 ^ eG i) (2 ^ (eG i + 1)) :=
    fun i => hen _ ((le_max_left _ _).trans (heG i))
  have hLone : Real.exp 1 ≤ (L : ℝ) :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hL
  have hz := hez eF eG
    (fun i => (le_max_left ez er).trans ((le_max_right en _).trans (heF i)))
    (fun i => (le_max_left ez er).trans ((le_max_right en _).trans (heG i))) L hLone hLF hLG
  have hr := her eF eG
    (fun i => (le_max_right ez er).trans ((le_max_right en _).trans (heF i)))
    (fun i => (le_max_right ez er).trans ((le_max_right en _).trans (heG i)))
    hmax hmain w L hw hL (hLF 0)
  have hm := commonPrimeEvent_leading_probability_split (w := w) F G
    (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG)
    (unequalDyadicPrimeMass_nonneg eF) (unequalDyadicPrimeMass_nonneg eG)
  rw [dyadic_leading_left_recursive_event eF eG hHF F G,
    dyadic_leading_right_recursive_event eF eG hHG F G] at hm
  have hlog := log_div_endpoint_le_log_div_sqrt hLone
  have hza := hz.1.trans (mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ 8 * ∑ i, ((integerPolynomialMainLeading F).degreeOf i : ℝ) by positivity))
  have hzb := hz.2.trans (mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ 8 * ∑ i, ((integerPolynomialMainLeading G).degreeOf i : ℝ) by positivity))
  unfold dyadicCommonPrimeMass dyadicRecurrenceSmall dyadicRecurrenceLarge
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, Nat.cast_add,
    Nat.cast_sum, div_eq_mul_inv] at hr hza hzb ⊢
  nlinarith only [hm, hza, hzb, hr]

end Hindman168
