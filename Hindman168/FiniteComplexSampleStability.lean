import Hindman168.FiniteComplexSetMean

/-! TRUE pointwise complex sample errors bound the ACTUAL finite mean
error. A genuine large signal survives actual freezing errors. -/
namespace Hindman168

theorem finite_complex_set_mean_sub {α : Type*} (S : Finset α) (f g : α → ℂ) :
    finiteComplexSetMean S (fun x => f x-g x)=finiteComplexSetMean S f-finiteComplexSetMean S g := by
  unfold finiteComplexSetMean
  rw [Finset.sum_sub_distrib,sub_div]

theorem finite_complex_sample_mean_error {α : Type*} (S : Finset α) (f g : α → ℂ)
    (ε : ℝ) (hε : 0 ≤ ε) (hError : ∀ x ∈ S, ‖f x-g x‖ ≤ ε) :
    ‖finiteComplexSetMean S f-finiteComplexSetMean S g‖ ≤ ε := by
  rw [← finite_complex_set_mean_sub]
  exact finiteComplexSetMean_norm_bound S _ ε hε hError

theorem finite_complex_frozen_mean_large {α : Type*} (S : Finset α) (f g : α → ℂ)
    (δ : ℝ) (hδ : 0 < δ) (hSignal : δ ≤ ‖finiteComplexSetMean S f‖)
    (hError : ∀ x ∈ S, ‖f x-g x‖ ≤ δ/4) :
    δ/2 < ‖finiteComplexSetMean S g‖ := by
  have hErr := finite_complex_sample_mean_error S f g (δ/4) (by positivity) hError
  have hTriangle : ‖finiteComplexSetMean S f‖ ≤
      ‖finiteComplexSetMean S f-finiteComplexSetMean S g‖+‖finiteComplexSetMean S g‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (finiteComplexSetMean S f-finiteComplexSetMean S g) (finiteComplexSetMean S g)
  linarith

end Hindman168
