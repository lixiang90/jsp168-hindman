import Hindman168.RoughScaledMonomials

namespace Hindman168
open scoped BigOperators

theorem rough_power_oscillation (x y B δ : ℝ) (n : ℕ)
    (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hx : |x| ≤ B) (hy : |y| ≤ B)
    (hxy : |x - y| ≤ δ) : |x ^ n - y ^ n| ≤ (n : ℝ) * δ * B ^ n := by
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : |x ^ n| ≤ B ^ n := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg x) hx n
    calc
      |x ^ (n + 1) - y ^ (n + 1)| =
          |x ^ n * (x - y) + (x ^ n - y ^ n) * y| := by
        congr 1
        simp only [pow_succ]
        ring
      _ ≤ |x ^ n| * |x - y| + |x ^ n - y ^ n| * |y| := by
        simpa only [abs_mul] using abs_add_le (x ^ n * (x - y)) ((x ^ n - y ^ n) * y)
      _ ≤ B ^ n * δ + ((n : ℝ) * δ * B ^ n) * B := by gcongr
      _ ≤ B ^ n * δ * B + ((n : ℝ) * δ * B ^ n) * B := by
        apply add_le_add _ le_rfl
        exact le_mul_of_one_le_right (mul_nonneg (pow_nonneg hB0 n) hδ) hB
      _ = ((n + 1 : ℕ) : ℝ) * δ * B ^ (n + 1) := by
        rw [Nat.cast_add, Nat.cast_one, pow_succ]
        ring

theorem rough_finite_power_product_bound {κ : Type*}
    (s : Finset κ) (I : κ → ℕ) (x : κ → ℝ) (B : ℝ)
    (hx : ∀ j ∈ s, |x j| ≤ B) :
    |∏ j ∈ s, x j ^ I j| ≤ B ^ (∑ j ∈ s, I j) := by
  rw [Finset.abs_prod]
  calc
    ∏ j ∈ s, |x j ^ I j| ≤ ∏ j ∈ s, B ^ I j := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro j hj
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hx j hj) _
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

theorem rough_finite_monomial_oscillation {κ : Type*}
    (s : Finset κ) (I : κ → ℕ) (x y : κ → ℝ) (B δ : ℝ)
    (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hx : ∀ j ∈ s, |x j| ≤ B) (hy : ∀ j ∈ s, |y j| ≤ B)
    (hxy : ∀ j ∈ s, |x j - y j| ≤ δ) :
    |(∏ j ∈ s, x j ^ I j) - ∏ j ∈ s, y j ^ I j| ≤
      (∑ j ∈ s, I j : ℕ) * δ * B ^ (∑ j ∈ s, I j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hsx := fun k hk => hx k (Finset.mem_insert_of_mem hk)
    have hsy := fun k hk => hy k (Finset.mem_insert_of_mem hk)
    have hsxy := fun k hk => hxy k (Finset.mem_insert_of_mem hk)
    have hp := rough_finite_power_product_bound s I y B hsy
    have hjx : |x j ^ I j| ≤ B ^ I j := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hx j (Finset.mem_insert_self _ _)) _
    have hjxy := rough_power_oscillation (x j) (y j) B δ (I j) hB hδ
      (hx j (Finset.mem_insert_self _ _)) (hy j (Finset.mem_insert_self _ _))
      (hxy j (Finset.mem_insert_self _ _))
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    calc
      |x j ^ I j * (∏ k ∈ s, x k ^ I k) - y j ^ I j * ∏ k ∈ s, y k ^ I k| =
          |x j ^ I j * ((∏ k ∈ s, x k ^ I k) - ∏ k ∈ s, y k ^ I k) +
            (x j ^ I j - y j ^ I j) * ∏ k ∈ s, y k ^ I k| := by congr 1; ring
      _ ≤ |x j ^ I j| * |(∏ k ∈ s, x k ^ I k) - ∏ k ∈ s, y k ^ I k| +
          |x j ^ I j - y j ^ I j| * |∏ k ∈ s, y k ^ I k| := by
        simpa only [abs_mul] using abs_add_le
          (x j ^ I j * ((∏ k ∈ s, x k ^ I k) - ∏ k ∈ s, y k ^ I k))
          ((x j ^ I j - y j ^ I j) * ∏ k ∈ s, y k ^ I k)
      _ ≤ B ^ I j * ((∑ k ∈ s, I k : ℕ) * δ * B ^ (∑ k ∈ s, I k)) +
          ((I j : ℝ) * δ * B ^ I j) * B ^ (∑ k ∈ s, I k) := by
        exact add_le_add
          (mul_le_mul hjx (ih hsx hsy hsxy) (abs_nonneg _) (by positivity))
          (mul_le_mul hjxy hp (abs_nonneg _) (by positivity))
      _ = ((I j + ∑ k ∈ s, I k : ℕ) : ℝ) * δ * B ^ (I j + ∑ k ∈ s, I k) := by
        rw [Nat.cast_add, pow_add]
        ring

end Hindman168
