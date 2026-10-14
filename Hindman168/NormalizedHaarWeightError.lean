import Hindman168.FiniteHaarCauchySchwarz
import Mathlib.Tactic.FieldSimp

namespace Hindman168
open scoped BigOperators

theorem finiteHaarMean_abs_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) : |finiteHaarMean f| ≤ C := by
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [finiteHaarMean, abs_div, abs_of_pos hc, div_le_iff₀ hc]
  calc
    _ ≤ ∑ x, |f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : α, C := Finset.sum_le_sum (fun x _ => hf x)
    _ = _ := by simp [mul_comm]

theorem normalizedHaarWeight_error {α : Type*} [Fintype α] [Nonempty α]
    (w : α → ℝ) (l u : ℝ) (hl : 0 < l) (hw : ∀ x, l ≤ w x ∧ w x ≤ u) (x : α) :
    |w x / finiteHaarMean w - 1| ≤ (u - l) / l := by
  have hm : l ≤ finiteHaarMean w := by
    simpa only [finiteHaarMean_const] using finiteHaarMean_mono (fun _ : α => l) w (fun x => (hw x).1)
  have hM : finiteHaarMean w ≤ u := by
    simpa only [finiteHaarMean_const] using finiteHaarMean_mono w (fun _ : α => u) (fun x => (hw x).2)
  have hp := hl.trans_le hm
  have hab : |w x - finiteHaarMean w| ≤ u - l := by
    rw [abs_le]
    constructor <;> linarith [(hw x).1, (hw x).2]
  rw [div_sub_one hp.ne', abs_div, abs_of_pos hp]
  exact (div_le_div_of_nonneg_right hab hp.le).trans
    (div_le_div_of_nonneg_left (by linarith : 0 ≤ u - l) hl hm)

theorem finiteHaarDensity_test_error {α : Type*} [Fintype α] [Nonempty α]
    (r F : α → ℝ) (ε : ℝ) (hr : ∀ x, |r x - 1| ≤ ε) (hF : ∀ x, |F x| ≤ 1) :
    |finiteHaarMean (fun x => r x * F x) - finiteHaarMean F| ≤ ε := by
  have he : finiteHaarMean (fun x => (r x - 1) * F x) =
      finiteHaarMean (fun x => r x * F x) - finiteHaarMean F := by
    unfold finiteHaarMean
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, sub_div]
  rw [← he]
  apply finiteHaarMean_abs_le
  intro x
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (hF x)).trans (hr x)

theorem normalizedHaar_test_eq_ratio {α : Type*} [Fintype α] [Nonempty α]
    (w F : α → ℝ) :
    finiteHaarMean (fun x => (w x / finiteHaarMean w) * F x) =
      (∑ x, w x * F x) / (∑ x, w x) := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he (x : α) : (w x / finiteHaarMean w) * F x =
      (w x * F x) * (finiteHaarMean w)⁻¹ := by ring
  simp only [he]
  rw [finiteHaarMean_mul_const, ← div_eq_mul_inv]
  unfold finiteHaarMean
  exact div_div_div_cancel_right₀ hc _ _

end Hindman168
