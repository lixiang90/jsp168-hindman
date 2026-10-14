import Hindman168.PowerUnitLaw
import Mathlib.Data.Nat.Prime.Basic

/-!
# Finite Euler exclusions for the actual power-unit normalizer

Multiplication by a positive W-unit gives the exact mass of its multiples.
Excluding a new prime therefore multiplies the original infinite normalizer
by its Euler factor. No prime-independence assumption is used.
-/

namespace Hindman168

open scoped BigOperators

theorem powerUnitWeight_mul_of_coprime (s : ℝ) (W d n : ℕ)
    (hd : d.Coprime W) :
    powerUnitWeight s W (d * n) =
      (d : ℝ) ^ (-s) * powerUnitWeight s W n := by
  by_cases hn : n.Coprime W
  · have hdn : (d * n).Coprime W := Nat.coprime_mul_iff_left.mpr ⟨hd, hn⟩
    rw [powerUnitWeight, if_pos hdn, powerUnitWeight, if_pos hn, Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hdn : ¬(d * n).Coprime W := fun h => hn (Nat.coprime_mul_iff_left.mp h).2
    simp only [powerUnitWeight, if_neg hdn, if_neg hn, mul_zero]

theorem powerUnitWeight_divisible_summable {s : ℝ} (hs : 1 < s) (W d : ℕ) :
    Summable (fun n : ℕ => if d ∣ n then powerUnitWeight s W n else 0) := by
  apply (powerUnitWeight_summable hs W).of_nonneg_of_le
  · intro n
    split_ifs
    · exact powerUnitWeight_nonneg s W n
    · exact le_rfl
  · intro n
    split_ifs
    · exact le_rfl
    · exact powerUnitWeight_nonneg s W n

theorem powerUnitWeight_divisible_tsum {s : ℝ} (hs : 1 < s)
    (W d : ℕ) (hdpos : 0 < d) (hd : d.Coprime W) :
    (∑' n : ℕ, if d ∣ n then powerUnitWeight s W n else 0) =
      (d : ℝ) ^ (-s) * powerUnitNormalizer s W := by
  classical
  have hi : Function.Injective (fun n : ℕ => d * n) := by
    intro x y h
    exact mul_left_cancel₀ hdpos.ne' h
  have hr : Function.support
      (fun n : ℕ => if d ∣ n then powerUnitWeight s W n else 0) ⊆
      Set.range (fun n : ℕ => d * n) := by
    intro n hn
    by_cases hdn : d ∣ n
    · rcases hdn with ⟨m, hm⟩
      exact ⟨m, hm.symm⟩
    · exact False.elim (hn (by simp [hdn]))
  rw [← hi.tsum_eq hr]
  simp only [dvd_mul_right, if_true, powerUnitWeight_mul_of_coprime s W d _ hd]
  exact (powerUnitWeight_summable hs W).tsum_mul_left _

theorem powerUnitNormalizer_mul_prime {s : ℝ} (hs : 1 < s)
    (W p : ℕ) (hp : p.Prime) (hc : p.Coprime W) :
    powerUnitNormalizer s (W * p) =
      (1 - (p : ℝ) ^ (-s)) * powerUnitNormalizer s W := by
  have hsplit : ∀ n : ℕ, powerUnitWeight s W n =
      powerUnitWeight s (W * p) n +
        (if p ∣ n then powerUnitWeight s W n else 0) := by
    intro n
    have hnp : n.Coprime p ↔ ¬p ∣ n := by
      rw [Nat.coprime_comm]
      exact hp.coprime_iff_not_dvd
    simp only [powerUnitWeight, Nat.coprime_mul_iff_right, hnp]
    by_cases hnW : n.Coprime W <;> by_cases hpn : p ∣ n <;> simp [hnW, hpn]
  have ht : (∑' n : ℕ, powerUnitWeight s W n) =
      ∑' n : ℕ, (powerUnitWeight s (W * p) n +
        (if p ∣ n then powerUnitWeight s W n else 0)) := tsum_congr hsplit
  rw [(powerUnitWeight_summable hs (W * p)).tsum_add
    (powerUnitWeight_divisible_summable hs W p),
    powerUnitWeight_divisible_tsum hs W p hp.pos hc] at ht
  change powerUnitNormalizer s W = powerUnitNormalizer s (W * p) +
    (p : ℝ) ^ (-s) * powerUnitNormalizer s W at ht
  nlinarith

theorem powerUnitNormalizer_one (s : ℝ) :
    powerUnitNormalizer s 1 = ∑' n : ℕ, (n : ℝ) ^ (-s) := by
  simp [powerUnitNormalizer, powerUnitWeight]

theorem powerUnitNormalizer_prime_product {s : ℝ} (hs : 1 < s)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    powerUnitNormalizer s (∏ p ∈ S, p) =
      (∑' n : ℕ, (n : ℝ) ^ (-s)) * ∏ p ∈ S, (1 - (p : ℝ) ^ (-s)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [powerUnitNormalizer_one]
  | @insert p S hpS ih =>
      have hp : p.Prime := hS p (Finset.mem_insert_self _ _)
      have ht : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
      have hc : p.Coprime (∏ q ∈ S, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        exact (hp.coprime_iff_not_dvd).mpr (by
          intro hd
          exact hpS ((Nat.prime_dvd_prime_iff_eq hp (ht q hq)).mp hd ▸ hq))
      rw [Finset.prod_insert hpS, mul_comm p, powerUnitNormalizer_mul_prime hs _ p hp hc,
        ih ht, Finset.prod_insert hpS]
      ring

theorem powerUnitNormalizer_mul_prime_product {s : ℝ} (hs : 1 < s)
    (W : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hW : ∀ p ∈ S, p.Coprime W) :
    powerUnitNormalizer s (W * ∏ p ∈ S, p) =
      powerUnitNormalizer s W * ∏ p ∈ S, (1 - (p : ℝ) ^ (-s)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
      have hp : p.Prime := hS p (Finset.mem_insert_self _ _)
      have ht : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
      have hc : p.Coprime (W * ∏ q ∈ S, q) := by
        apply Nat.coprime_mul_iff_right.mpr
        refine ⟨hW p (Finset.mem_insert_self _ _), Nat.Coprime.prod_right ?_⟩
        intro q hq
        exact (hp.coprime_iff_not_dvd).mpr (by
          intro hd
          exact hpS ((Nat.prime_dvd_prime_iff_eq hp (ht q hq)).mp hd ▸ hq))
      have he : W * (p * ∏ q ∈ S, q) = (W * ∏ q ∈ S, q) * p := by ring
      rw [Finset.prod_insert hpS, he, powerUnitNormalizer_mul_prime hs _ p hp hc,
        ih ht (fun q hq => hW q (Finset.mem_insert_of_mem hq)), Finset.prod_insert hpS]
      ring

end Hindman168
