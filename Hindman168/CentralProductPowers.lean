import Hindman168.CentralCommutatorPowers
import Mathlib.Data.Nat.Choose.Basic

/-! Genuine finite power collection for the specified central
commutator, including the exact binomial correction and its divisibility
at twice a chosen denominator. No subgroup normality is used. -/

namespace Hindman168
open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem nat_power_swap_of_central_commutator (a b : G)
    (hc : ⁅a, b⁆ ∈ Subgroup.center G) (n : ℕ) :
    b ^ n * a = (⁅a, b⁆ ^ n)⁻¹ * a * b ^ n := by
  have he : ⁅a, b⁆ ^ n * (b ^ n * a) = a * b ^ n := by
    rw [← commutator_nat_pow_right_of_central a b hc n]
    simp only [commutatorElement_def, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  calc
    b ^ n * a = (⁅a, b⁆ ^ n)⁻¹ * (⁅a, b⁆ ^ n * (b ^ n * a)) := by simp
    _ = (⁅a, b⁆ ^ n)⁻¹ * (a * b ^ n) := congrArg ((⁅a, b⁆ ^ n)⁻¹ * ·) he
    _ = _ := by rw [mul_assoc]

theorem product_nat_pow_of_central_commutator (a b : G)
    (hc : ⁅a, b⁆ ∈ Subgroup.center G) (n : ℕ) :
    (a * b) ^ n = (⁅a, b⁆ ^ (n.choose 2))⁻¹ * a ^ n * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := nat_power_swap_of_central_commutator a b hc n
    have hz : (⁅a, b⁆ ^ n)⁻¹ ∈ Subgroup.center G :=
      (Subgroup.center G).inv_mem ((Subgroup.center G).pow_mem hc n)
    have hm : a ^ n * (⁅a, b⁆ ^ n)⁻¹ = (⁅a, b⁆ ^ n)⁻¹ * a ^ n :=
      Subgroup.mem_center_iff.mp hz (a ^ n)
    have hchoose : (n + 1).choose 2 = n + n.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ n 1
    calc
      (a * b) ^ (n + 1) =
          (⁅a, b⁆ ^ (n.choose 2))⁻¹ * (a ^ n * (b ^ n * a)) * b := by
        rw [pow_succ, ih]
        simp only [mul_assoc]
      _ = (⁅a, b⁆ ^ (n.choose 2))⁻¹ *
          ((a ^ n * (⁅a, b⁆ ^ n)⁻¹) * a * b ^ n) * b := by
        rw [hs]
        simp only [mul_assoc]
      _ = (⁅a, b⁆ ^ (n.choose 2))⁻¹ *
          (((⁅a, b⁆ ^ n)⁻¹ * a ^ n) * a * b ^ n) * b := by rw [hm]
      _ = (⁅a, b⁆ ^ ((n + 1).choose 2))⁻¹ * a ^ (n + 1) * b ^ (n + 1) := by
        simp only [hchoose, pow_add, mul_inv_rev, pow_one, mul_assoc]

theorem twice_denominator_choose_two (k : ℕ) :
    (2 * k).choose 2 = k * (2 * k - 1) := by
  rw [Nat.choose_two_right]
  have he : 2 * k * (2 * k - 1) = (k * (2 * k - 1)) * 2 :=
    (Nat.mul_assoc 2 k (2 * k - 1)).trans (Nat.mul_comm 2 (k * (2 * k - 1)))
  rw [he]
  simp

end Hindman168
