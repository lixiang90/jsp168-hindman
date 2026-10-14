import Hindman168.FiniteComplexMassMean

namespace Hindman168
open scoped BigOperators Classical

theorem rough_two_sample_haar_obstruction (x y mean : ℂ) (η : ℝ)
    (h : η ≤ ‖x-y‖) : η/2 ≤ ‖x-mean‖ ∨ η/2 ≤ ‖y-mean‖ := by
  have ht : ‖x-y‖ ≤ ‖x-mean‖+‖y-mean‖ := by
    calc
      _ = ‖(x-mean)-(y-mean)‖ := congrArg norm (by ring)
      _ ≤ _ := norm_sub_le _ _
  by_cases hx : η/2 ≤ ‖x-mean‖
  · exact Or.inl hx
  · right
    have hxl := lt_of_not_ge hx
    linarith

theorem rough_haar_obstruction_perturbation (x y mean : ℂ) (η δ : ℝ)
    (h : η ≤ ‖x-mean‖) (herr : ‖x-y‖ ≤ δ) : η-δ ≤ ‖y-mean‖ := by
  have ht : ‖x-mean‖ ≤ ‖x-y‖+‖y-mean‖ := by
    calc
      _ = ‖(x-y)+(y-mean)‖ := congrArg norm (by ring)
      _ ≤ _ := norm_add_le _ _
  linarith

/-- Some positive-weight component has at least the full Haar discrepancy.
This incurs no loss depending on the number of cubes. -/
theorem rough_convex_haar_obstruction {ι : Type*} (s : Finset ι)
    (weight : ι → ℝ) (m : ι → ℂ) (mean : ℂ)
    (hw : ∀ i ∈ s, 0 ≤ weight i) (htotal : ∑ i ∈ s, weight i = 1) :
    ∃ i ∈ s, 0 < weight i ∧
      ‖(∑ j ∈ s, (weight j : ℂ)*m j)-mean‖ ≤ ‖m i-mean‖ := by
  let T := s.filter (fun i => 0 < weight i)
  have hT : T.Nonempty := by
    by_contra h
    have hz : ∀ i ∈ s, weight i = 0 := by
      intro i hi
      apply le_antisymm _ (hw i hi)
      apply le_of_not_gt
      intro hpos
      exact h ⟨i, Finset.mem_filter.mpr ⟨hi, hpos⟩⟩
    have hs : ∑ i ∈ s, weight i = 0 := Finset.sum_eq_zero hz
    linarith
  obtain ⟨i, hi, hmax⟩ := T.exists_max_image (fun j => ‖m j-mean‖) hT
  have hit := Finset.mem_filter.mp hi
  refine ⟨i, hit.1, hit.2, ?_⟩
  have he : (∑ j ∈ s, (weight j : ℂ)*m j)-mean =
      ∑ j ∈ s, (weight j : ℂ)*(m j-mean) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, htotal, Complex.ofReal_one, one_mul]
  rw [he]
  calc
    _ ≤ ∑ j ∈ s, ‖(weight j : ℂ)*(m j-mean)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ s, weight j*‖m i-mean‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw j hj)]
      by_cases hpos : 0 < weight j
      · exact mul_le_mul_of_nonneg_left (hmax j (Finset.mem_filter.mpr ⟨hj, hpos⟩)) (hw j hj)
      · have hz : weight j = 0 := le_antisymm (le_of_not_gt hpos) (hw j hj)
        simp [hz]
    _ = _ := by rw [← Finset.sum_mul, htotal, one_mul]

end Hindman168
