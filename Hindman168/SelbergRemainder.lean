import Hindman168.SelbergWeightBounds

/-!
# Uniform remainder control for Lambda-squared sieves

The finite divisor reindexing follows the Lambda-squared calculation in
mathlib's SelbergSieve (Arend Mellendijk, Apache 2.0). It is proved here
as a usable general identity. A uniform remainder bound E costs at most
E times the square of the L1 norm of the underlying Selberg weights.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem sum_divisor_lcm_pairs {P : ℕ} (hP : P ≠ 0) (f : ℕ → ℕ → ℝ) :
    (∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
      if d = Nat.lcm a b then f a b else 0) =
        ∑ a ∈ P.divisors, ∑ b ∈ P.divisors, f a b := by
  have he : (∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
      if d = Nat.lcm a b then f a b else 0) =
      ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        if d = Nat.lcm a b then f a b else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdP := Nat.dvd_of_mem_divisors hd
    have hi : ∀ a b,
        (a ∣ d ∧ b ∣ d ∧ d = Nat.lcm a b) = (d = Nat.lcm a b) := by
      simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hP hdP, Finset.sum_filter,
      Finset.ite_sum_zero, ← ite_and, hi]
  rw [he, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_ite_eq_of_mem'
  exact Nat.mem_divisors.mpr
    ⟨Nat.lcm_dvd_iff.mpr ⟨Nat.dvd_of_mem_divisors ha, Nat.dvd_of_mem_divisors hb⟩, hP⟩

theorem lambdaSquared_abs_sum_le {P : ℕ} (hP : P ≠ 0) (w : ℕ → ℝ) :
    (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d|) ≤
      (∑ d ∈ P.divisors, |w d|) ^ 2 := by
  calc
    _ ≤ ∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d = Nat.lcm a b then |w a| * |w b| else 0 := by
      apply Finset.sum_le_sum
      intro d _
      rw [BoundingSieve.lambdaSquared]
      calc
        _ ≤ ∑ a ∈ d.divisors,
            |∑ b ∈ d.divisors, if d = Nat.lcm a b then w a * w b else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
            |if d = Nat.lcm a b then w a * w b else 0| :=
          Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
        _ = _ := by simp only [apply_ite abs, abs_zero, abs_mul]
    _ = ∑ a ∈ P.divisors, ∑ b ∈ P.divisors, |w a| * |w b| :=
      sum_divisor_lcm_pairs hP _
    _ = _ := by rw [sq, Finset.sum_mul]; simp only [Finset.mul_sum]

theorem lambdaSquared_errSum_le (s : BoundingSieve) (w : ℕ → ℝ) {E : ℝ}
    (hE : 0 ≤ E) (hrem : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ E) :
    s.errSum (BoundingSieve.lambdaSquared w) ≤
      E * (∑ d ∈ s.prodPrimes.divisors, |w d|) ^ 2 := by
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors, |BoundingSieve.lambdaSquared w d| * E :=
      Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left (hrem d hd) (abs_nonneg _))
    _ = (∑ d ∈ s.prodPrimes.divisors, |BoundingSieve.lambdaSquared w d|) * E :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ d ∈ s.prodPrimes.divisors, |w d|) ^ 2 * E :=
      mul_le_mul_of_nonneg_right (lambdaSquared_abs_sum_le s.prodPrimes_ne_zero w) hE
    _ = _ := mul_comm _ _

theorem optimalSelbergWeight_errSum_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hnu : ∀ d, d ∣ s.prodPrimes → d ≤ z → (s.nu d)⁻¹ ≤ (d : ℝ))
    {E : ℝ} (hE : 0 ≤ E) (hrem : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ E) :
    s.errSum (BoundingSieve.lambdaSquared (optimalSelbergWeight s z)) ≤ E * (z : ℝ) ^ 4 := by
  have hs := optimalSelbergWeight_abs_sum_le s hz hnu
  have hnonneg : 0 ≤ ∑ d ∈ s.prodPrimes.divisors, |optimalSelbergWeight s z d| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc
    _ ≤ E * (∑ d ∈ s.prodPrimes.divisors, |optimalSelbergWeight s z d|) ^ 2 :=
      lambdaSquared_errSum_le s _ hE hrem
    _ ≤ E * ((z : ℝ) ^ 2) ^ 2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hnonneg hs 2) hE
    _ = _ := by ring

theorem siftedSum_le_selberg_uniform_remainder (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hnu : ∀ d, d ∣ s.prodPrimes → d ≤ z → (s.nu d)⁻¹ ≤ (d : ℝ))
    {E : ℝ} (hE : 0 ≤ E) (hrem : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ E) :
    s.siftedSum ≤ s.totalMass / selbergDenominator s z + E * (z : ℝ) ^ 4 :=
  (siftedSum_le_optimalSelberg s hz).trans
    (add_le_add le_rfl (optimalSelbergWeight_errSum_le s hz hnu hE hrem))

end Hindman168
