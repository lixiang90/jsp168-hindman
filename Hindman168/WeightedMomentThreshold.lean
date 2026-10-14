import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Hindman168
open scoped BigOperators Classical

theorem weighted_power_threshold {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) (r : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    (∑ i, p i * f i ^ r) - τ ^ r ≤ ∑ i, if τ ≤ f i then p i else 0 := by
  have hpoint (i : ι) : p i * f i ^ r ≤ p i * τ ^ r + if τ ≤ f i then p i else 0 := by
    by_cases hi : τ ≤ f i
    · rw [if_pos hi]
      have hm : p i * f i ^ r ≤ p i :=
        mul_le_of_le_one_right (hp i) (pow_le_one₀ (hf i).1 (hf i).2)
      have hn := mul_nonneg (hp i) (pow_nonneg hτ r)
      linarith
    · rw [if_neg hi, add_zero]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hf i).1 (le_of_not_ge hi) r) (hp i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hpoint i)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul] at hs
  linarith

theorem weighted_power_half_mass {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) (r : ℕ) (hr : 0 < r)
    (δ : ℝ) (hδ : 0 ≤ δ) (hm : δ ^ r ≤ ∑ i, p i * f i ^ r) :
    δ ^ r / 2 ≤ ∑ i, if δ / 2 ≤ f i then p i else 0 := by
  have hs := weighted_power_threshold p f hp hsum hf r (δ / 2) (by positivity)
  have htwo : (2 : ℝ) ≤ 2 ^ r := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
    simpa using hh
  have hhalf : (δ / 2) ^ r ≤ δ ^ r / 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (pow_nonneg hδ r) (by norm_num) htwo
  linarith

end Hindman168
