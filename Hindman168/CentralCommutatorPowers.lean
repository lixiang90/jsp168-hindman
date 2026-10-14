import Mathlib.GroupTheory.Commutator.Basic

/-! Actual power collection when the specified commutator is central.
These identities do not require the selected subgroup to be normal and
will supply the bilinear power step in successive nilpotent layers. -/

namespace Hindman168
open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_nat_pow_left_of_central (a b : G)
    (hc : ⁅a, b⁆ ∈ Subgroup.center G) (n : ℕ) :
    ⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, commutatorElement_mul_left_eq_conj_mul, ih]
    have he : a ^ n * ⁅a, b⁆ = ⁅a, b⁆ * a ^ n :=
      Subgroup.mem_center_iff.mp hc (a ^ n)
    rw [he]
    simp only [mul_assoc, mul_inv_cancel, mul_one, pow_succ']

theorem commutator_nat_pow_right_of_central (a b : G)
    (hc : ⁅a, b⁆ ∈ Subgroup.center G) (n : ℕ) :
    ⁅a, b ^ n⁆ = ⁅a, b⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, commutatorElement_mul_right_eq_mul_conj, ih]
    have he : b ^ n * ⁅a, b⁆ = ⁅a, b⁆ * b ^ n :=
      Subgroup.mem_center_iff.mp hc (b ^ n)
    rw [mul_assoc (⁅a, b⁆ ^ n) (b ^ n) ⁅a, b⁆, he]
    simp only [mul_assoc, mul_inv_cancel, mul_one, pow_succ]

theorem commutator_nat_powers_of_central (a b : G)
    (hc : ⁅a, b⁆ ∈ Subgroup.center G) (m n : ℕ) :
    ⁅a ^ m, b ^ n⁆ = ⁅a, b⁆ ^ (m * n) := by
  have hl := commutator_nat_pow_left_of_central a b hc m
  have hm : ⁅a ^ m, b⁆ ∈ Subgroup.center G :=
    hl.symm ▸ (Subgroup.center G).pow_mem hc m
  rw [commutator_nat_pow_right_of_central (a ^ m) b hm n, hl, ← pow_mul]

end Hindman168
