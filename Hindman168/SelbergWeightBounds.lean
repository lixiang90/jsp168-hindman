import Hindman168.SelbergOptimalWeights
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Truncation and absolute bounds for the explicit Selberg weights

On divisors of P, the diagonal coordinates have total absolute mass 1.
Möbius inversion therefore bounds each weight by 1/nu(d), and all weights
above the cutoff vanish. For the density nu(d)=1/d this gives the coarse
but uniform L1 bound z^2 used to control the interval sieve remainder.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem selbergDiagonal_abs (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) {l : ℕ}
    (hl : l ∣ s.prodPrimes) :
    |selbergDiagonal s z l| =
      if l ≤ z then s.selbergTerms l / selbergDenominator s z else 0 := by
  by_cases hlz : l ≤ z
  · have hmu : |(ArithmeticFunction.moebius l : ℝ)| = 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
        (s.squarefree_of_dvd_prodPrimes hl)
    simp only [selbergDiagonal, if_pos hlz, abs_div, abs_mul, hmu,
      abs_of_pos (s.selbergTerms_pos hl), abs_of_pos (selbergDenominator_pos s hz), one_mul]
  · simp only [selbergDiagonal, if_neg hlz, abs_zero]

theorem selbergDiagonal_abs_sum (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    (∑ l ∈ s.prodPrimes.divisors, |selbergDiagonal s z l|) = 1 := by
  have he : ∀ l ∈ s.prodPrimes.divisors,
      |selbergDiagonal s z l| =
        (if l ≤ z then s.selbergTerms l else 0) / selbergDenominator s z := by
    intro l hl
    rw [selbergDiagonal_abs s hz (Nat.dvd_of_mem_divisors hl)]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl he, ← Finset.sum_div, ← Finset.sum_filter]
  change selbergDenominator s z / selbergDenominator s z = 1
  exact div_self (selbergDenominator_pos s hz).ne'

theorem reverseSelbergDiagonal_abs_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    {d : ℕ} (hd : d ∣ s.prodPrimes) :
    |reverseDivisorMoebius s.prodPrimes (selbergDiagonal s z) (s.prodPrimes / d)| ≤ 1 := by
  rw [reverseDivisorMoebius_eq_upper s.prodPrimes_ne_zero hd]
  calc
    _ ≤ ∑ l ∈ s.prodPrimes.divisors,
        |if d ∣ l then (ArithmeticFunction.moebius (l / d) : ℝ) *
          selbergDiagonal s z l else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ s.prodPrimes.divisors, |selbergDiagonal s z l| := by
      apply Finset.sum_le_sum
      intro l _
      by_cases hdl : d ∣ l
      · rw [if_pos hdl, abs_mul]
        have hmu : |(ArithmeticFunction.moebius (l / d) : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := l / d)
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hmu (abs_nonneg (selbergDiagonal s z l))
      · rw [if_neg hdl, abs_zero]
        exact abs_nonneg _
    _ = 1 := selbergDiagonal_abs_sum s hz

theorem optimalSelbergWeight_abs_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    {d : ℕ} (hd : d ∣ s.prodPrimes) :
    |optimalSelbergWeight s z d| ≤ (s.nu d)⁻¹ := by
  rw [optimalSelbergWeight, if_pos hd, abs_mul,
    abs_of_pos (inv_pos.mpr (s.nu_pos_of_dvd_prodPrimes hd))]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (reverseSelbergDiagonal_abs_le s hz hd)
    (inv_nonneg.mpr (s.nu_pos_of_dvd_prodPrimes hd).le)

theorem optimalSelbergWeight_eq_zero_of_cutoff (s : BoundingSieve) {z d : ℕ}
    (hzd : z < d) : optimalSelbergWeight s z d = 0 := by
  by_cases hd : d ∣ s.prodPrimes
  · rw [optimalSelbergWeight, if_pos hd,
      reverseDivisorMoebius_eq_upper s.prodPrimes_ne_zero hd]
    have he : (∑ l ∈ s.prodPrimes.divisors, if d ∣ l then
        (ArithmeticFunction.moebius (l / d) : ℝ) * selbergDiagonal s z l else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      by_cases hdl : d ∣ l
      · have hlpos := Nat.pos_of_mem_divisors hl
        have hdz : z < l := hzd.trans_le (Nat.le_of_dvd hlpos hdl)
        simp only [if_pos hdl, selbergDiagonal, if_neg (not_le.mpr hdz), mul_zero]
      · simp only [if_neg hdl]
    rw [he, mul_zero]
  · simp only [optimalSelbergWeight, if_neg hd]

theorem selbergDivisorWindow_card_le (s : BoundingSieve) (z : ℕ) :
    (selbergDivisorWindow s z).card ≤ z := by
  have hs : selbergDivisorWindow s z ⊆ Finset.Icc 1 z := by
    intro d hd
    exact Finset.mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2⟩
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hs

theorem optimalSelbergWeight_abs_sum_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hnu : ∀ d, d ∣ s.prodPrimes → d ≤ z → (s.nu d)⁻¹ ≤ (d : ℝ)) :
    (∑ d ∈ s.prodPrimes.divisors, |optimalSelbergWeight s z d|) ≤ (z : ℝ) ^ 2 := by
  have he : (∑ d ∈ s.prodPrimes.divisors, |optimalSelbergWeight s z d|) =
      ∑ d ∈ selbergDivisorWindow s z, |optimalSelbergWeight s z d| := by
    rw [selbergDivisorWindow, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hdz : d ≤ z
    · simp only [if_pos hdz]
    · simp only [if_neg hdz, optimalSelbergWeight_eq_zero_of_cutoff s (not_le.mp hdz), abs_zero]
  rw [he]
  calc
    _ ≤ ∑ _d ∈ selbergDivisorWindow s z, (z : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdP := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
      have hdz := (Finset.mem_filter.mp hd).2
      exact (optimalSelbergWeight_abs_le s hz hdP).trans
        ((hnu d hdP hdz).trans (by exact_mod_cast hdz))
    _ = ((selbergDivisorWindow s z).card : ℝ) * z := by simp
    _ ≤ (z : ℝ) * z := mul_le_mul_of_nonneg_right
      (by exact_mod_cast selbergDivisorWindow_card_le s z) (Nat.cast_nonneg z)
    _ = _ := (sq (z : ℝ)).symm

end Hindman168
