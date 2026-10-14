import Hindman168.PrimeValuationVectors

/-!
# Exact finite-prime valuation masses under the actual comparison law

The finite joint formula follows by removing the specified prime-power
divisor and then applying the proved finite Euler exclusions. It establishes
prime independence for the original countable law, rather than assuming it.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem powerUnitWeight_valuation_vector_tsum {s : ℝ} (hs : 1 < s)
    (W : ℕ) (S : Finset ℕ) (a : ℕ → ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hW : ∀ p ∈ S, p.Coprime W) :
    (∑' n : ℕ, if ∀ p ∈ S, n.factorization p = a p then
      powerUnitWeight s W n else 0) =
      (primeValuationDivisor S a : ℝ) ^ (-s) *
        powerUnitNormalizer s (W * ∏ p ∈ S, p) := by
  classical
  have hi : Function.Injective (fun n : ℕ => primeValuationDivisor S a * n) :=
    fun _ _ h => mul_left_cancel₀ (primeValuationDivisor_ne_zero S a hS) h
  have hr : Function.support (fun n : ℕ =>
      if ∀ p ∈ S, n.factorization p = a p then powerUnitWeight s W n else 0) ⊆
      Set.range (fun n : ℕ => primeValuationDivisor S a * n) := by
    intro n hn
    by_cases ha : ∀ p ∈ S, n.factorization p = a p
    · have hn0 : n ≠ 0 := by
        intro hz
        subst n
        exact hn (by simp [powerUnitWeight_zero hs])
      obtain ⟨m, hm, _, _⟩ := exists_coprime_remainder_of_valuations S a hS n hn0 ha
      exact ⟨m, hm.symm⟩
    · exact False.elim (hn (by simp [ha]))
  have hf : ∀ m : ℕ,
      (if ∀ p ∈ S, (primeValuationDivisor S a * m).factorization p = a p then
        powerUnitWeight s W (primeValuationDivisor S a * m) else 0) =
      (primeValuationDivisor S a : ℝ) ^ (-s) *
        powerUnitWeight s (W * ∏ p ∈ S, p) m := by
    intro m
    by_cases hm : m = 0
    · subst m
      simp [powerUnitWeight_zero hs]
    · simp only [primeValuationDivisor_mul_exact_iff S a hS m hm]
      rw [powerUnitWeight_mul_of_coprime s W _ m (primeValuationDivisor_coprime S a W hW)]
      by_cases hmS : m.Coprime (∏ p ∈ S, p)
      · rw [if_pos hmS]
        by_cases hmW : m.Coprime W
        · have hc : m.Coprime (W * ∏ p ∈ S, p) :=
            Nat.coprime_mul_iff_right.mpr ⟨hmW, hmS⟩
          rw [powerUnitWeight, if_pos hmW, powerUnitWeight, if_pos hc]
        · have hc : ¬m.Coprime (W * ∏ p ∈ S, p) :=
            fun h => hmW (Nat.coprime_mul_iff_right.mp h).1
          rw [powerUnitWeight, if_neg hmW, powerUnitWeight, if_neg hc]
      · have hc : ¬m.Coprime (W * ∏ p ∈ S, p) :=
          fun h => hmS (Nat.coprime_mul_iff_right.mp h).2
        rw [if_neg hmS, powerUnitWeight, if_neg hc, mul_zero]
  rw [← hi.tsum_eq hr]
  rw [tsum_congr hf]
  exact (powerUnitWeight_summable hs _).tsum_mul_left _

theorem primeValuationDivisor_rpow (s : ℝ) (S : Finset ℕ) (a : ℕ → ℕ) :
    (primeValuationDivisor S a : ℝ) ^ (-s) =
      ∏ p ∈ S, ((p : ℝ) ^ (-s)) ^ a p := by
  classical
  unfold primeValuationDivisor
  rw [Nat.cast_prod, ← Real.finsetProd_rpow]
  · apply Finset.prod_congr rfl
    intro p _
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _) (a p), mul_comm,
      Real.rpow_mul_natCast (Nat.cast_nonneg _)]
  · intro p _
    positivity

theorem powerUnitProbability_valuation_vector_tsum {s : ℝ} (hs : 1 < s)
    (W : ℕ) (S : Finset ℕ) (a : ℕ → ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hW : ∀ p ∈ S, p.Coprime W) :
    (∑' n : ℕ, if ∀ p ∈ S, n.factorization p = a p then
      powerUnitProbability s W n else 0) =
      ∏ p ∈ S, ((1 - (p : ℝ) ^ (-s)) * ((p : ℝ) ^ (-s)) ^ a p) := by
  classical
  have he : ∀ n : ℕ,
      (if ∀ p ∈ S, n.factorization p = a p then powerUnitProbability s W n else 0) =
      (if ∀ p ∈ S, n.factorization p = a p then powerUnitWeight s W n else 0) /
        powerUnitNormalizer s W := by
    intro n
    split_ifs <;> simp [powerUnitProbability]
  rw [tsum_congr he, tsum_div_const, powerUnitWeight_valuation_vector_tsum hs W S a hS hW,
    powerUnitNormalizer_mul_prime_product hs W S hS hW, primeValuationDivisor_rpow s S a]
  rw [Finset.prod_mul_distrib]
  field_simp [(powerUnitNormalizer_pos hs W).ne']

theorem powerUnitProbability_valuation_tsum {s : ℝ} (hs : 1 < s)
    (W p a : ℕ) (hp : p.Prime) (hW : p.Coprime W) :
    (∑' n : ℕ, if n.factorization p = a then powerUnitProbability s W n else 0) =
      (1 - (p : ℝ) ^ (-s)) * ((p : ℝ) ^ (-s)) ^ a := by
  simpa using powerUnitProbability_valuation_vector_tsum hs W {p} (fun _ => a)
    (by simpa using hp) (by simpa using hW)

end Hindman168
