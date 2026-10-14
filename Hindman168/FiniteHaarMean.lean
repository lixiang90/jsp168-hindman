import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

/-! Exact normalized counting averages on nonempty finite types. -/
namespace Hindman168
open scoped BigOperators

noncomputable def finiteHaarMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

theorem finiteHaarMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    finiteHaarMean (fun _ : α => c) = c := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [finiteHaarMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c hc

theorem finiteHaarMean_abs_le_one {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (hf : ∀ x, |f x| ≤ 1) : |finiteHaarMean f| ≤ 1 := by
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [finiteHaarMean, abs_div, abs_of_pos hc, div_le_one hc]
  calc
    |∑ x, f x| ≤ ∑ x, |f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : α, (1 : ℝ) := Finset.sum_le_sum (fun x _ => hf x)
    _ = Fintype.card α := by simp

theorem finiteHaarMean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    finiteHaarMean (fun x => f x + g x) = finiteHaarMean f + finiteHaarMean g := by
  simp only [finiteHaarMean, Finset.sum_add_distrib, add_div]

end Hindman168
