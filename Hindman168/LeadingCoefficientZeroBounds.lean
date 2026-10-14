import Hindman168.LeadingCoefficientMarginals

/-!
# Uniform zero-event costs for specialized main leading coefficients

The main leading polynomial is nonzero before specialization. Its actual
tail law has one fewer independent prime coordinate. The retained weighted
Schwartz--Zippel estimate and PNT supply the zero-event costs uniformly in
all unequal dyadic endpoints, with no exceptional fiber discarded.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem exists_dyadic_prime_normalization_threshold :
    ∃ e0 : ℕ, ∀ e ≥ e0, 0 < primePoolHarmonicMass (2 ^ e) (2 ^ (e + 1)) := by
  obtain ⟨e0, he0⟩ := exists_uniform_dyadic_zero_threshold
  refine ⟨e0, ?_⟩
  intro e he
  have hlog : 0 < Real.log (2 ^ e : ℕ) :=
    Real.log_pos (by exact_mod_cast (by have := (he0 e he).1; omega : 1 < 2 ^ e))
  exact (one_div_pos.mpr (mul_pos (by norm_num) hlog)).trans_le (he0 e he).2

theorem exists_dyadic_leading_zero_threshold {m n : ℕ}
    {F : MvPolynomial (Fin (m + 1)) ℤ} {G : MvPolynomial (Fin (n + 1)) ℤ}
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ e0 : ℕ, ∀ (eF : Fin (m + 1) → ℕ) (eG : Fin (n + 1) → ℕ),
      (∀ i, e0 ≤ eF i) → (∀ i, e0 ≤ eG i) → ∀ L : ℕ,
      Real.exp 1 ≤ (L : ℝ) → (∀ i, L ≤ 2 ^ eF i) → (∀ i, L ≤ 2 ^ eG i) →
      event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
        (fun xy => MvPolynomial.eval (fun i => (Fin.tail xy.1 i : ℤ)) (integerPolynomialMainLeading F) = 0) ≤
          (8 * ∑ i, ((integerPolynomialMainLeading F).degreeOf i : ℝ)) * (Real.log (L : ℝ) / L) ∧
      event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
        (fun xy => MvPolynomial.eval (fun i => (Fin.tail xy.2 i : ℤ)) (integerPolynomialMainLeading G) = 0) ≤
          (8 * ∑ i, ((integerPolynomialMainLeading G).degreeOf i : ℝ)) * (Real.log (L : ℝ) / L) := by
  obtain ⟨ez, hez⟩ := exists_dyadic_prime_normalization_threshold
  obtain ⟨ea, hea⟩ := unequalDyadicPrime_polynomial_zero_uniform (integerPolynomialMainLeading_ne_zero hF)
  obtain ⟨eb, heb⟩ := unequalDyadicPrime_polynomial_zero_uniform (integerPolynomialMainLeading_ne_zero hG)
  let e0 := max ez (max ea eb)
  refine ⟨e0, ?_⟩
  intro eF eG heF heG L hL hLF hLG
  have hHF : ∀ i, 0 < primePoolHarmonicMass (2 ^ eF i) (2 ^ (eF i + 1)) :=
    fun i => hez _ ((le_max_left _ _).trans (heF i))
  have hHG : ∀ i, 0 < primePoolHarmonicMass (2 ^ eG i) (2 ^ (eG i + 1)) :=
    fun i => hez _ ((le_max_left _ _).trans (heG i))
  constructor
  · rw [dyadic_leading_zero_left_event eF eG hHF hHG F]
    exact hea (fun i => eF i.succ)
      (fun i => (le_max_left ea eb).trans ((le_max_right ez _).trans (heF i.succ)))
      L hL (fun i => hLF i.succ)
  · rw [dyadic_leading_zero_right_event eF eG hHF hHG G]
    exact heb (fun i => eG i.succ)
      (fun i => (le_max_right ea eb).trans ((le_max_right ez _).trans (heG i.succ)))
      L hL (fun i => hLG i.succ)

theorem log_div_endpoint_le_log_div_sqrt {L : ℕ} (hL : Real.exp 1 ≤ (L : ℝ)) :
    Real.log (L : ℝ) / L ≤ Real.log (L : ℝ) / Real.sqrt L := by
  have hLone : 1 < (L : ℝ) := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hL
  have hsqrt : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hs : Real.sqrt (L : ℝ) ≤ L := Real.sqrt_le_self_iff.mpr (Or.inr hLone.le)
  exact div_le_div_of_nonneg_left (Real.log_pos hLone).le hsqrt hs

end Hindman168
