import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Arithmetic checks for the paper's master scales

The binary weights are written in increasing-exponent order. Reversing this
order gives the paper's `2^(N-j)` weights. These lemmas check the arithmetic
mechanism; they do not assert the full asymptotic master-scales lemma.
-/

namespace Hindman168

open scoped BigOperators

def binaryWeight (S : Finset ℕ) : ℕ := ∑ j ∈ S, 2 ^ j

theorem binary_sum_add_one (n : ℕ) :
    (∑ j ∈ Finset.range n, (2 : ℕ) ^ j) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

theorem lower_weights_lt {k : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range k) : binaryWeight S < 2 ^ k := by
  have hle : binaryWeight S ≤ ∑ j ∈ Finset.range k, (2 : ℕ) ^ j :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (by intros; exact Nat.zero_le _)
  have hsum := binary_sum_add_one k
  omega

/-- One binary weight dominates the sum of all smaller distinct weights. -/
theorem binary_weight_separation {k : ℕ} {A B : Finset ℕ}
    (hk : k ∈ A) (hB : B ⊆ Finset.range k) : binaryWeight B < binaryWeight A := by
  have hsingle : (2 : ℕ) ^ k ≤ binaryWeight A :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((2 : ℕ) ^ j)) hk
  exact lt_of_lt_of_le (lower_weights_lt hB) hsingle

/-- Multiplying the individual scales is exactly the weighted-subset scale. -/
theorem product_scale (S : Finset ℕ) (W w : ℕ) :
    (∏ j ∈ S, W ^ (w * 2 ^ j)) = W ^ (w * binaryWeight S) := by
  unfold binaryWeight
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, Nat.mul_add, pow_add]

/-- The scale ratio includes a full factor `W^w`, without rational division. -/
theorem scale_divisibility {k : ℕ} {A B : Finset ℕ} (W w : ℕ)
    (hk : k ∈ A) (hB : B ⊆ Finset.range k) :
    W ^ (w * binaryWeight B) * W ^ w ∣ W ^ (w * binaryWeight A) := by
  have hweight : binaryWeight B + 1 ≤ binaryWeight A :=
    Nat.succ_le_of_lt (binary_weight_separation hk hB)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.mul_le_mul_left w hweight)
  refine ⟨W ^ d, ?_⟩
  rw [hd, Nat.mul_add, Nat.mul_one, pow_add, pow_add]

/-- Exact identity used to turn a residue shift into an own-target displacement. -/
theorem residue_shift_identity (t p m rho M delta q : ℤ)
    (hq : q = t * rho + M * delta) :
    t * (p + m * rho) + m * M * delta = t * p + m * q := by
  rw [hq]
  ring

end Hindman168
