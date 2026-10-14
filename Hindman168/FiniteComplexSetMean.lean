import Hindman168.FiniteComplexMean

namespace Hindman168
open scoped BigOperators Classical

noncomputable def finiteComplexSetMean {α : Type*} (s : Finset α) (f : α → ℂ) : ℂ :=
  (∑ a ∈ s, f a) / s.card

theorem finiteComplexSetMean_image {α β : Type*} [DecidableEq β] (s : Finset α)
    (g : α → β) (hg : Function.Injective g) (f : β → ℂ) :
    finiteComplexSetMean (s.image g) f = finiteComplexSetMean s (fun a => f (g a)) := by
  unfold finiteComplexSetMean
  rw [Finset.card_image_of_injective s hg, Finset.sum_image]
  exact fun _ _ _ _ h => hg h

theorem finiteComplexSetMean_mul_card {α : Type*} (s : Finset α) (f : α → ℂ) :
    finiteComplexSetMean s f * s.card = ∑ a ∈ s, f a := by
  by_cases hs : s.card = 0
  · have he := Finset.card_eq_zero.mp hs
    simp only [he, finiteComplexSetMean, Finset.sum_empty, Finset.card_empty,
      Nat.cast_zero, div_zero, mul_zero]
  · exact div_mul_cancel₀ _ (by exact_mod_cast hs)

theorem finite_complex_sum_norm_bound {α : Type*} (s : Finset α) (f : α → ℂ)
    (B : ℝ) (hf : ∀ a ∈ s, ‖f a‖ ≤ B) : ‖∑ a ∈ s, f a‖ ≤ s.card * B := by
  calc
    _ ≤ ∑ a ∈ s, ‖f a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ s, B := Finset.sum_le_sum hf
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem finiteComplexSetMean_norm_bound {α : Type*} (s : Finset α) (f : α → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ a ∈ s, ‖f a‖ ≤ B) :
    ‖finiteComplexSetMean s f‖ ≤ B := by
  by_cases hs : s.card = 0
  · simp only [finiteComplexSetMean, hs, Nat.cast_zero, div_zero, norm_zero]
    exact hB
  · have hc : (0 : ℝ) < s.card := by exact_mod_cast Nat.pos_of_ne_zero hs
    rw [finiteComplexSetMean, norm_div, Complex.norm_natCast]
    exact (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using finite_complex_sum_norm_bound s f B hf)

theorem finite_complex_sum_difference_bound {α : Type*} [DecidableEq α] (s t : Finset α)
    (f : α → ℂ) (B : ℝ) (hf : ∀ a, ‖f a‖ ≤ B) :
    ‖(∑ a ∈ s, f a) - ∑ a ∈ t, f a‖ ≤
      (((s \ t).card : ℝ) + (t \ s).card) * B := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff]
  have h := (norm_sub_le _ _).trans (add_le_add
    (finite_complex_sum_norm_bound (s \ t) f B (fun a _ => hf a))
    (finite_complex_sum_norm_bound (t \ s) f B (fun a _ => hf a)))
  simpa only [add_mul] using h

theorem finite_card_difference_bound {α : Type*} [DecidableEq α] (s t : Finset α) :
    |(t.card : ℝ) - s.card| ≤ ((s \ t).card : ℝ) + (t \ s).card := by
  have h : (s \ t).card + t.card = (t \ s).card + s.card := by
    rw [Finset.card_sdiff_add_card, Finset.card_sdiff_add_card, Finset.union_comm]
  have hr : ((s \ t).card : ℝ) + t.card = (t \ s).card + s.card := by exact_mod_cast h
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (s \ t).card,
    Nat.cast_nonneg (α := ℝ) (t \ s).card]

theorem finiteComplexSetMean_difference_bound {α : Type*} [DecidableEq α] (s t : Finset α)
    (hs : s.Nonempty) (f : α → ℂ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ a, ‖f a‖ ≤ B) :
    ‖finiteComplexSetMean s f - finiteComplexSetMean t f‖ ≤
      2 * B * (((s \ t).card : ℝ) + (t \ s).card) / s.card := by
  have hm : (s.card : ℂ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hmR : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have he : finiteComplexSetMean s f - finiteComplexSetMean t f =
      ((∑ a ∈ s, f a) - (∑ a ∈ t, f a) +
        ((t.card : ℂ) - s.card) * finiteComplexSetMean t f) / s.card := by
    apply (eq_div_iff hm).mpr
    linear_combination finiteComplexSetMean_mul_card s f - finiteComplexSetMean_mul_card t f
  have hc : ‖(t.card : ℂ) - s.card‖ = |(t.card : ℝ) - s.card| := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  rw [he, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ hmR.le
  calc
    _ ≤ ‖(∑ a ∈ s, f a) - ∑ a ∈ t, f a‖ +
        ‖((t.card : ℂ) - s.card) * finiteComplexSetMean t f‖ := norm_add_le _ _
    _ ≤ (((s \ t).card : ℝ) + (t \ s).card) * B +
        (((s \ t).card : ℝ) + (t \ s).card) * B := by
      apply add_le_add (finite_complex_sum_difference_bound s t f B hf)
      rw [norm_mul, hc]
      exact mul_le_mul (finite_card_difference_bound s t)
        (finiteComplexSetMean_norm_bound t f B hB (fun a _ => hf a)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Hindman168
