import Hindman168.AdmissibleCellProbabilities

namespace Hindman168
open scoped BigOperators

theorem finite_nonnegative_weighted_test_bound {α : Type*} (S : Finset α) (m f : α → ℝ)
    (hm : ∀ x, 0 ≤ m x) (hf : ∀ x, |f x| ≤ 1) :
    |∑ x ∈ S, m x * f x| ≤ ∑ x ∈ S, m x := by
  calc
    _ ≤ ∑ x ∈ S, |m x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (hm x)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf x) (hm x)

theorem finite_retained_probability_test_error {α : Type*} [DecidableEq α]
    (S T : Finset α) (hST : S ⊆ T) (m f : α → ℝ)
    (hm : ∀ x, 0 ≤ m x) (hf : ∀ x, |f x| ≤ 1)
    (ht : ∑ x ∈ T, m x = 1) (hs : 0 < ∑ x ∈ S, m x) :
    |(∑ x ∈ T, m x * f x) - (∑ x ∈ S, m x * f x) / (∑ x ∈ S, m x)| ≤
      2 * ∑ x ∈ T \ S, m x := by
  let a := ∑ x ∈ S, m x * f x
  let b := ∑ x ∈ T \ S, m x * f x
  let p := ∑ x ∈ S, m x
  let d := ∑ x ∈ T \ S, m x
  have ha : |a| ≤ p := finite_nonnegative_weighted_test_bound S m f hm hf
  have hb : |b| ≤ d := finite_nonnegative_weighted_test_bound (T \ S) m f hm hf
  have hd : 0 ≤ d := Finset.sum_nonneg (fun x _ => hm x)
  have hp : 0 < p := hs
  have hpd : d + p = 1 := (Finset.sum_sdiff hST).trans ht
  have he : (∑ x ∈ T, m x * f x) = b + a := (Finset.sum_sdiff hST).symm
  have halg : a - a / p = -(a * (d / p)) := by
    apply (eq_neg_iff_add_eq_zero).mpr
    field_simp
    rw [show p - 1 + d = 0 by linarith]
    ring
  have hab : |a - a / p| ≤ d := by
    rw [halg, abs_neg, abs_mul, abs_of_nonneg (div_nonneg hd hp.le)]
    calc
      _ ≤ p * (d / p) := mul_le_mul_of_nonneg_right ha (div_nonneg hd hp.le)
      _ = d := mul_div_cancel₀ _ (ne_of_gt hp)
  rw [he]
  change |b + a - a / p| ≤ 2 * d
  calc
    _ = |b + (a - a / p)| := by ring_nf
    _ ≤ |b| + |a - a / p| := abs_add_le _ _
    _ ≤ 2 * d := by linarith

end Hindman168
