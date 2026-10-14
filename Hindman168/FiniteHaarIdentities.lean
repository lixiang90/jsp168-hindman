import Hindman168.FiniteHaarMean
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic.Ring

namespace Hindman168
open scoped BigOperators

theorem finiteHaarMean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : finiteHaarMean (fun x => f (e x)) = finiteHaarMean f := by
  unfold finiteHaarMean
  rw [e.sum_comp, Fintype.card_congr e]

theorem finiteHaarMean_mul_const {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    finiteHaarMean (fun x => f x * c) = finiteHaarMean f * c := by
  unfold finiteHaarMean
  rw [← Finset.sum_mul]
  ring

theorem finiteHaarMean_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    finiteHaarMean (fun x => c * f x) = c * finiteHaarMean f := by
  unfold finiteHaarMean
  rw [← Finset.mul_sum]
  ring

theorem finiteHaarMean_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    finiteHaarMean (fun x => finiteHaarMean (f x)) =
      finiteHaarMean (fun y => finiteHaarMean (fun x => f x y)) := by
  unfold finiteHaarMean
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_comm]
  ring

theorem finiteHaarMean_nonneg {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ finiteHaarMean f :=
  div_nonneg (Finset.sum_nonneg (fun x _ => hf x)) (Nat.cast_nonneg _)

theorem finiteHaarMean_add_left {G : Type*} [AddGroup G] [Fintype G]
    (f : G → ℝ) (a : G) : finiteHaarMean (fun x => f (a + x)) = finiteHaarMean f :=
  finiteHaarMean_equiv (Equiv.addLeft a) f

end Hindman168

