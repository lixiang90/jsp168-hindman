import Hindman168.CoprimeMultipleSubgroups
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Combine subgroup statistics with original finite probability weights.
The loss is exactly bounded by the probability of a noncoprime pair. -/
namespace Hindman168
open scoped BigOperators Classical

theorem multiple_subgroup_statistic_bound {G : Type*} [AddCommGroup G]
    (Φ : AddSubgroup G → ℝ) (h0 : 0 ≤ Φ ⊤) (h1 : ∀ Q, Φ Q ≤ 1) (a b : ℕ) :
    Φ (multipleAddSubgroup G a ⊔ multipleAddSubgroup G b) ≤
      Φ ⊤ + if a.Coprime b then 0 else 1 := by
  by_cases h : a.Coprime b
  · rw [coprime_multiple_subgroups_sup G a b h, if_pos h, add_zero]
  · rw [if_neg h]
    exact (h1 _).trans (by linarith)

theorem weighted_multiple_subgroup_bound {G ι : Type*} [AddCommGroup G] [Fintype ι]
    (p : ι → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) (q : ι → ℕ)
    (Φ : AddSubgroup G → ℝ) (h0 : 0 ≤ Φ ⊤) (h1 : ∀ Q, Φ Q ≤ 1) :
    (∑ a, ∑ b, p a * p b * Φ (multipleAddSubgroup G (q a) ⊔ multipleAddSubgroup G (q b))) ≤
      Φ ⊤ + ∑ a, ∑ b, p a * p b * (if (q a).Coprime (q b) then 0 else 1) := by
  have hc : (∑ a, ∑ b, p a * p b * Φ ⊤) = Φ ⊤ := by
    calc
      _ = ∑ a, p a * (∑ b, p b * Φ ⊤) := by simp only [Finset.mul_sum, mul_assoc]
      _ = Φ ⊤ := by simp only [← Finset.sum_mul, hsum, one_mul]
  calc
    _ ≤ ∑ a, ∑ b, p a * p b * (Φ ⊤ + if (q a).Coprime (q b) then 0 else 1) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (multiple_subgroup_statistic_bound Φ h0 h1 (q a) (q b))
        (mul_nonneg (hp a) (hp b))
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib, hc]

end Hindman168
