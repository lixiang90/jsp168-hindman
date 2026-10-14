import Hindman168.FiniteHaarIdentities
import Mathlib.Tactic.Linarith

namespace Hindman168
open scoped BigOperators

theorem finiteHaarMean_mono {α : Type*} [Fintype α] (f g : α → ℝ)
    (h : ∀ x, f x ≤ g x) : finiteHaarMean f ≤ finiteHaarMean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (Nat.cast_nonneg _)

theorem finiteHaarMean_cauchy_schwarz {α : Type*} [Fintype α] (f g : α → ℝ) :
    finiteHaarMean (fun x => f x * g x) ^ 2 ≤
      finiteHaarMean (fun x => f x ^ 2) * finiteHaarMean (fun x => g x ^ 2) := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α) f g
  have hd := div_le_div_of_nonneg_right hs (sq_nonneg (Fintype.card α : ℝ))
  simpa only [finiteHaarMean, div_pow, div_mul_div_comm, pow_two] using hd

theorem finiteHaarMean_square_le {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    finiteHaarMean f ^ 2 ≤ finiteHaarMean (fun x => f x ^ 2) := by
  simpa only [mul_one, one_pow, finiteHaarMean_const] using
    finiteHaarMean_cauchy_schwarz f (fun _ => 1)

theorem finiteHaarMean_discard_unit_factor {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    finiteHaarMean (fun x => f x * g x) ^ 2 ≤ finiteHaarMean (fun x => g x ^ 2) := by
  have hb : finiteHaarMean (fun x => f x ^ 2) ≤ 1 := by
    calc
      _ ≤ finiteHaarMean (fun _ : α => (1 : ℝ)) := finiteHaarMean_mono _ _
        (fun x => by simpa only [sq_abs] using pow_le_one₀ (abs_nonneg (f x)) (hf x) (n := 2))
      _ = 1 := finiteHaarMean_const 1
  have hg := finiteHaarMean_nonneg (fun x => g x ^ 2) (fun x => sq_nonneg (g x))
  exact (finiteHaarMean_cauchy_schwarz f g).trans (mul_le_of_le_one_left hg hb)

end Hindman168
