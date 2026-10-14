import Hindman168.RoughComplexFiberMean

namespace Hindman168
open scoped BigOperators Classical

theorem rough_complex_boundary_haar_selection {α ι : Type*} [Fintype ι]
    (S T : Finset α) (hS : S.Nonempty) (hTS : T ⊆ S)
    (hdiscard : (S \ T).card < S.card)
    (label : α → ι) (f : α → ℂ) (mean : ℂ) (B η δ : ℝ)
    (hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B)
    (hboundary : 2*B*((S \ T).card : ℝ)/S.card ≤ δ)
    (hbad : η ≤ ‖finiteComplexSetMean S f-mean‖) :
    ∃ i : ι, (T.filter (fun x => label x = i)).Nonempty ∧
      η-δ ≤ ‖finiteComplexSetMean (T.filter (fun x => label x = i)) f-mean‖ := by
  have hT : T.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.sdiff_empty] at hdiscard
    omega
  have herr : ‖finiteComplexSetMean S f-finiteComplexSetMean T f‖ ≤ δ := by
    have h := finiteComplexSetMean_difference_bound S T hS f B hB hf
    have he : T \ S = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hTS
    simp only [he, Finset.card_empty, Nat.cast_zero, add_zero] at h
    exact h.trans hboundary
  have hgap := rough_haar_obstruction_perturbation (finiteComplexSetMean S f)
    (finiteComplexSetMean T f) mean η δ hbad herr
  obtain ⟨i, hi, hg⟩ := rough_complex_fiber_haar_selection T hT label f mean
  exact ⟨i, hi, hgap.trans hg⟩

end Hindman168
