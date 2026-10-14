import Hindman168.CentralProductPowers
import Hindman168.PositiveSubgroupRoots

/-! Positive roots multiply when their actual commutator is central,
without any normality assumption on the specified subgroup. The explicit
power is twice the product of the original positive denominators. -/

namespace Hindman168
open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem subgroup_product_double_power_of_central_commutator (Γ : Subgroup G)
    (a b : G) (hc : ⁅a, b⁆ ∈ Subgroup.center G) (m n : ℕ)
    (ha : a ^ m ∈ Γ) (hb : b ^ n ∈ Γ) :
    (a * b) ^ (2 * (m * n)) ∈ Γ := by
  have hcomm : ⁅a, b⁆ ^ (m * n) ∈ Γ := by
    rw [← commutator_nat_powers_of_central a b hc m n]
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem ha hb) (Γ.inv_mem ha)) (Γ.inv_mem hb)
  have hcorr : (⁅a, b⁆ ^ ((2 * (m * n)).choose 2))⁻¹ ∈ Γ := by
    rw [twice_denominator_choose_two, pow_mul]
    exact Γ.inv_mem (Γ.pow_mem hcomm _)
  have ham : a ^ (2 * (m * n)) ∈ Γ := by
    rw [Nat.mul_left_comm 2 m n, pow_mul]
    exact Γ.pow_mem ha _
  have hbn : b ^ (2 * (m * n)) ∈ Γ := by
    rw [Nat.mul_comm m n, Nat.mul_left_comm 2 n m, pow_mul]
    exact Γ.pow_mem hb _
  rw [product_nat_pow_of_central_commutator a b hc]
  exact Γ.mul_mem (Γ.mul_mem hcorr ham) hbn

theorem positiveSubgroupRoots_mul_of_central_commutator (Γ : Subgroup G) {a b : G}
    (ha : a ∈ positiveSubgroupRoots Γ) (hb : b ∈ positiveSubgroupRoots Γ)
    (hc : ⁅a, b⁆ ∈ Subgroup.center G) : a * b ∈ positiveSubgroupRoots Γ := by
  obtain ⟨m, hm, ham⟩ := ha
  obtain ⟨n, hn, hbn⟩ := hb
  refine ⟨2 * (m * n), Nat.mul_pos (by decide) (Nat.mul_pos hm hn), ?_⟩
  exact subgroup_product_double_power_of_central_commutator Γ a b hc m n ham hbn

end Hindman168
