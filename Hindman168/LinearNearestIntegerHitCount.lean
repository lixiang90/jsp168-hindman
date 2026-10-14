import Hindman168.FiniteIntegerSpanCard
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Round

namespace Hindman168
open scoped BigOperators Classical

/-- Count actual integer indices lying in one actual lifted interval.
The inequality includes zero and negative slopes without division. -/
theorem linear_integer_lift_fiber_count (s : Finset ℕ) (b a ε : ℝ) (hε : 0 ≤ ε)
    (m : ℤ) (hhit : ∀ j ∈ s, |b+(j : ℝ)*a-(m : ℝ)| ≤ ε) :
    |a| *(s.card : ℝ) ≤ |a|+2*ε := by
  by_cases hs : s.Nonempty
  · have hmax := abs_le.mp (hhit (s.max' hs) (s.max'_mem hs))
    have hmin := abs_le.mp (hhit (s.min' hs) (s.min'_mem hs))
    have hd : |((s.max' hs : ℝ)-(s.min' hs : ℝ))*a| ≤ 2*ε := by
      rw [abs_le]
      constructor <;> nlinarith [hmax.1, hmax.2, hmin.1, hmin.2]
    have hlo : (s.min' hs : ℝ) ≤ (s.max' hs : ℝ) := by
      exact_mod_cast s.min'_le_max' hs
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hlo)] at hd
    have hc := mul_le_mul_of_nonneg_left (finite_natural_span_card s hs) (abs_nonneg a)
    nlinarith
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [hz, Finset.card_empty, Nat.cast_zero, mul_zero]
    positivity

theorem linear_nearest_integer_label_count (s : Finset ℕ) (J : ℕ)
    (hsJ : s ⊆ Finset.range J) (b a ε : ℝ) (hε : 0 ≤ ε)
    (hhit : ∀ j ∈ s, |b+(j : ℝ)*a-(round (b+(j : ℝ)*a) : ℝ)| ≤ ε) :
    ((s.image (fun j : ℕ => round (b+(j : ℝ)*a))).card : ℝ) ≤ |a| *(J : ℝ)+2*ε+1 := by
  let t := s.image (fun j : ℕ => round (b+(j : ℝ)*a))
  by_cases ht : t.Nonempty
  · obtain ⟨j, hj, hjm⟩ := Finset.mem_image.mp (t.max'_mem ht)
    obtain ⟨i, hi, him⟩ := Finset.mem_image.mp (t.min'_mem ht)
    have hjr : (j : ℝ) ≤ J := by exact_mod_cast (Finset.mem_range.mp (hsJ hj)).le
    have hir : (i : ℝ) ≤ J := by exact_mod_cast (Finset.mem_range.mp (hsJ hi)).le
    have hdist : |(j : ℝ)-(i : ℝ)| ≤ J := by
      rw [abs_le]
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i, Nat.cast_nonneg (α := ℝ) j]
    have hmul : |((j : ℝ)-(i : ℝ))*a| ≤ (J : ℝ)*|a| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hdist (abs_nonneg a)
    have hmax := abs_le.mp (hhit j hj)
    have hmin := abs_le.mp (hhit i hi)
    have hspan : (t.max' ht : ℝ)-(t.min' ht : ℝ) ≤ |a| *(J : ℝ)+2*ε := by
      rw [← hjm, ← him]
      have hh := le_abs_self (((j : ℝ)-(i : ℝ))*a)
      nlinarith [hmax.1, hmax.2, hmin.1, hmin.2]
    exact (finite_integer_span_card t ht).trans (by linarith)
  · have hz := Finset.not_nonempty_iff_eq_empty.mp ht
    change (t.card : ℝ) ≤ _
    rw [hz, Finset.card_empty, Nat.cast_zero]
    positivity

/-- Actual nearest-integer interval hits, counted by their actual lift labels.
The division-free statement remains valid for a zero slope. -/
theorem linear_nearest_integer_hit_count (s : Finset ℕ) (J : ℕ)
    (hsJ : s ⊆ Finset.range J) (b a ε : ℝ) (hε : 0 ≤ ε)
    (hhit : ∀ j ∈ s, |b+(j : ℝ)*a-(round (b+(j : ℝ)*a) : ℝ)| ≤ ε) :
    |a| *(s.card : ℝ) ≤ (|a| *(J : ℝ)+2*ε+1)*(|a|+2*ε) := by
  let label := fun j : ℕ => round (b+(j : ℝ)*a)
  have hc := Finset.card_eq_sum_card_image label s
  have hcr := congrArg (fun n : ℕ => (n : ℝ)) hc
  push_cast at hcr
  rw [hcr, Finset.mul_sum]
  calc
    _ ≤ ∑ m ∈ s.image label, (|a|+2*ε) := by
      apply Finset.sum_le_sum
      intro m _
      apply linear_integer_lift_fiber_count _ b a ε hε m
      intro j hj
      have h := Finset.mem_filter.mp hj
      have he : round (b+(j : ℝ)*a) = m := h.2
      simpa only [he] using hhit j h.1
    _ = ((s.image label).card : ℝ)*(|a|+2*ε) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (linear_nearest_integer_label_count s J hsJ b a ε hε hhit) (by positivity)

end Hindman168

