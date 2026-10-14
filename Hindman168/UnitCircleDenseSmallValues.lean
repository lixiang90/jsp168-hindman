import Hindman168.UnitCircleNormBump

namespace Hindman168
open scoped BigOperators Classical Topology
open MeasureTheory

theorem unit_circle_dense_bump_mean {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f : α → UnitAddCircle) (c ε δ : ℝ) (hε : ε ≤ c)
    (hdense : δ*(s.card : ℝ) ≤ (s.filter (fun a => ‖f a‖ ≤ ε)).card) :
    δ*(c-ε) ≤ (∑ a ∈ s, unitCircleNormBump c (f a))/(s.card : ℝ) := by
  have hcε : 0 ≤ c-ε := sub_nonneg.mpr hε
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hsum : ((s.filter (fun a => ‖f a‖ ≤ ε)).card : ℝ)*(c-ε) ≤
      ∑ a ∈ s, unitCircleNormBump c (f a) := by
    calc
      _ = ∑ _a ∈ s.filter (fun a => ‖f a‖ ≤ ε), (c-ε) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ s.filter (fun a => ‖f a‖ ≤ ε), unitCircleNormBump c (f a) := by
        apply Finset.sum_le_sum
        intro a ha
        exact (sub_le_sub_left (Finset.mem_filter.mp ha).2 c).trans (le_max_right _ _)
      _ ≤ ∑ a ∈ s, unitCircleNormBump c (f a) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun a _ _ => unit_circle_norm_bump_nonneg c (f a))
  apply (le_div_iff₀ hc).mpr
  have hmul := mul_le_mul_of_nonneg_right hdense hcε
  nlinarith

theorem unit_circle_bump_complex_mean {α : Type*} (s : Finset α) (f : α → UnitAddCircle)
    (c : ℝ) : finiteComplexSetMean s (fun a => unitCircleNormBumpObservable c (f a)) =
      (((∑ a ∈ s, unitCircleNormBump c (f a))/(s.card : ℝ) : ℝ) : ℂ) := by
  simp only [finiteComplexSetMean, unitCircleNormBumpObservable, ContinuousMap.coe_mk,
    Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

/-- Actual dense modular small values force true Haar discrepancy for one
fixed bump, uniformly over the orbit and epsilon. -/
theorem unit_circle_small_values_discrepancy (x b : ℝ) (N : ℕ) (hN : 0 < N)
    (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : ε ≤ δ/10)
    (hdense : δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
      ‖((b+(n : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ ε)).card) :
    δ^2/40 ≤ ‖finiteComplexSetMean (Finset.range N)
      (fun n => unitCircleNormBumpObservable (δ/4)
        (((b+(n : ℝ)*x : ℝ) : UnitAddCircle))) -
          ∫ t, unitCircleNormBumpObservable (δ/4) t ∂AddCircle.haarAddCircle‖ := by
  have hm := unit_circle_dense_bump_mean (Finset.range N)
    (Finset.nonempty_range_iff.mpr hN.ne')
    (fun n => ((b+(n : ℝ)*x : ℝ) : UnitAddCircle)) (δ/4) ε δ
    (by linarith) (by simpa using hdense)
  have hi := unit_circle_norm_bump_haar_bound (δ/4) (by positivity) (by linarith)
  rw [unit_circle_bump_complex_mean]
  change δ^2/40 ≤ ‖((_ : ℝ) : ℂ)-∫ t, (unitCircleNormBump (δ/4) t : ℂ)
    ∂AddCircle.haarAddCircle‖
  have hreal : (∫ t, (unitCircleNormBump (δ/4) t : ℂ) ∂AddCircle.haarAddCircle) =
      ((∫ t, unitCircleNormBump (δ/4) t ∂AddCircle.haarAddCircle : ℝ) : ℂ) :=
    integral_ofReal
  rw [hreal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have he : δ*(δ/4-δ/10) ≤ δ*(δ/4-ε) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hε _) hδ.le
  exact (by nlinarith [hm, hi] : δ^2/40 ≤
    (∑ n ∈ Finset.range N, unitCircleNormBump (δ/4)
      (((b+(n : ℝ)*x : ℝ) : UnitAddCircle)))/(↑(Finset.range N).card : ℝ) -
        ∫ t, unitCircleNormBump (δ/4) t ∂AddCircle.haarAddCircle).trans (le_abs_self _)

/-- Coarse recurrence with an actual fixed bound before the slope, offset,
length and small-value tolerance are chosen. -/
theorem unit_circle_dense_small_values_coarse_inverse (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ (x b : ℝ) (N : ℕ), 0 < N → ∀ ε : ℝ,
      ε ≤ δ/10 →
      δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
        ‖((b+(n : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ ε)).card →
      ∃ k : ℤ, 0 < k.natAbs ∧ k.natAbs ≤ A ∧
        (N : ℝ)*‖(((k : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨A, hA, hinv⟩ := unit_circle_affine_linear_inverse (δ^2/40) (by positivity)
  refine ⟨A, hA, ?_⟩
  intro x b N hN ε hε hdense
  exact hinv x b N hN (unitCircleNormBumpObservable (δ/4))
    (unit_circle_norm_bump_observable_admissible (δ/4) (by positivity) (by linarith))
    (unit_circle_small_values_discrepancy x b N hN δ ε hδ hδ1 hε hdense)

end Hindman168
