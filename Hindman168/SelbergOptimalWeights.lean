import Hindman168.DivisorUpperInversion
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Explicit truncated Selberg weights

The weights are obtained by Möbius inversion of the optimal diagonal
coordinates. Their normalization and main sum are proved from the actual
finite divisor sums. A positive cutoff containing 1 gives main term 1/G.
No interval distribution or Brun--Titchmarsh input is assumed here.
-/

namespace Hindman168

open scoped BigOperators Classical

def selbergDivisorWindow (s : BoundingSieve) (z : ℕ) : Finset ℕ :=
  s.prodPrimes.divisors.filter (fun d => d ≤ z)

noncomputable def selbergDenominator (s : BoundingSieve) (z : ℕ) : ℝ :=
  ∑ d ∈ selbergDivisorWindow s z, s.selbergTerms d

noncomputable def selbergDiagonal (s : BoundingSieve) (z l : ℕ) : ℝ :=
  if l ≤ z then (ArithmeticFunction.moebius l : ℝ) * s.selbergTerms l /
    selbergDenominator s z else 0

noncomputable def optimalSelbergWeight (s : BoundingSieve) (z d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes then (s.nu d)⁻¹ *
    reverseDivisorMoebius s.prodPrimes (selbergDiagonal s z) (s.prodPrimes / d) else 0

theorem selbergDenominator_pos (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    0 < selbergDenominator s z := by
  apply Finset.sum_pos
  · intro d hd
    exact s.selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)
  · exact ⟨1, Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨one_dvd _, s.prodPrimes_ne_zero⟩, hz⟩⟩

theorem selbergDiagonal_moebius_sum (s : BoundingSieve) (z : ℕ) :
    (∑ d ∈ s.prodPrimes.divisors,
      (ArithmeticFunction.moebius d : ℝ) * selbergDiagonal s z d) =
        selbergDenominator s z / selbergDenominator s z := by
  change _ = (∑ d ∈ selbergDivisorWindow s z, s.selbergTerms d) /
    selbergDenominator s z
  rw [selbergDivisorWindow, Finset.sum_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hsq : (ArithmeticFunction.moebius d : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
      (s.squarefree_of_dvd_prodPrimes (Nat.dvd_of_mem_divisors hd))
  by_cases hz : d ≤ z
  · simp only [selbergDiagonal, if_pos hz]
    calc
      _ = ((ArithmeticFunction.moebius d : ℝ) ^ 2) * s.selbergTerms d /
          selbergDenominator s z := by ring
      _ = _ := by rw [hsq, one_mul]
  · simp only [selbergDiagonal, if_neg hz, mul_zero, zero_div]

theorem optimalSelbergWeight_one (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    optimalSelbergWeight s z 1 = 1 := by
  rw [optimalSelbergWeight, if_pos (one_dvd _), Nat.div_one,
    s.nu_mult.map_one, inv_one, one_mul,
    reverseDivisorMoebius_at_top s.prodPrimes_ne_zero,
    selbergDiagonal_moebius_sum, div_self (selbergDenominator_pos s hz).ne']

theorem optimalSelbergWeight_transform (s : BoundingSieve) (z : ℕ) {l : ℕ}
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d then s.nu d * optimalSelbergWeight s z d else 0) =
        selbergDiagonal s z l := by
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then reverseDivisorMoebius s.prodPrimes (selbergDiagonal s z)
          (s.prodPrimes / d) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdP := Nat.dvd_of_mem_divisors hd
      simp only [optimalSelbergWeight, if_pos hdP]
      rw [← mul_assoc, mul_inv_cancel₀ (s.nu_ne_zero hdP), one_mul]
    _ = _ := upper_divisor_moebius_inversion s.prodPrimes_ne_zero hl _

theorem optimalSelbergWeight_mainSum (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.mainSum (BoundingSieve.lambdaSquared (optimalSelbergWeight s z)) =
      1 / selbergDenominator s z := by
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have ht : ∀ l ∈ s.prodPrimes.divisors,
      (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors,
          if l ∣ d then s.nu d * optimalSelbergWeight s z d else 0) ^ 2 =
      (if l ≤ z then s.selbergTerms l else 0) / selbergDenominator s z ^ 2 := by
    intro l hl
    have hlP := Nat.dvd_of_mem_divisors hl
    rw [optimalSelbergWeight_transform s z hlP]
    have hsq : (ArithmeticFunction.moebius l : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (s.squarefree_of_dvd_prodPrimes hlP)
    by_cases hlz : l ≤ z
    · simp only [selbergDiagonal, if_pos hlz, div_pow, mul_pow, hsq, one_mul]
      field_simp [(s.selbergTerms_pos hlP).ne', (selbergDenominator_pos s hz).ne']
    · simp only [selbergDiagonal, if_neg hlz, zero_pow (by decide : 2 ≠ 0),
        mul_zero, zero_div]
  rw [Finset.sum_congr rfl ht, ← Finset.sum_div, ← Finset.sum_filter]
  change selbergDenominator s z / selbergDenominator s z ^ 2 = _
  field_simp [(selbergDenominator_pos s hz).ne']

theorem siftedSum_le_optimalSelberg (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.siftedSum ≤ s.totalMass / selbergDenominator s z +
      s.errSum (BoundingSieve.lambdaSquared (optimalSelbergWeight s z)) := by
  have h := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared (optimalSelbergWeight s z))
    (BoundingSieve.upperMoebius_lambdaSquared _ (optimalSelbergWeight_one s hz))
  simpa only [optimalSelbergWeight_mainSum s hz, div_eq_mul_inv, one_mul] using h

end Hindman168
