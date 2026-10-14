import Hindman168.ComplexMeanObservableApproximation
import Hindman168.CompactLipschitzApproximation

/-! Actual empirical comparison for all fixed Lipschitz tests extends to every
continuous test on a compact metric space, without changing the sample sequence. -/
namespace Hindman168
open Filter
open scoped Topology

theorem continuous_empirical_comparison_of_lipschitz {X α β : Type*}
    [MetricSpace X] [CompactSpace X] (S : ℕ → Finset α) (T : ℕ → Finset β)
    (x : ℕ → α → X) (y : ℕ → β → X)
    (h : ∀ F : C(X,ℂ), ∀ K : NNReal, LipschitzWith K F →
      Tendsto (fun m => finiteComplexSetMean (S m) (fun a => F (x m a)) -
        finiteComplexSetMean (T m) (fun b => F (y m b))) atTop (𝓝 0)) (F : C(X,ℂ)) :
    Tendsto (fun m => finiteComplexSetMean (S m) (fun a => F (x m a)) -
      finiteComplexSetMean (T m) (fun b => F (y m b))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨G,⟨K,hK⟩,hclose⟩ := compact_lipschitz_uniform_approximation X F (ε/4) (by positivity)
  filter_upwards [Metric.tendsto_nhds.mp (h G K hK) (ε/4) (by positivity)] with m hm
  simp only [dist_zero_right] at hm ⊢
  have hS := finite_complex_set_mean_observable_difference (S m) (fun a => F (x m a))
    (fun a => G (x m a)) (ε/4) (by positivity)
    (fun a _ => (ContinuousMap.norm_coe_le_norm (F-G) (x m a)).trans hclose.le)
  have hT := finite_complex_set_mean_observable_difference (T m) (fun b => F (y m b))
    (fun b => G (y m b)) (ε/4) (by positivity)
    (fun b _ => (ContinuousMap.norm_coe_le_norm (F-G) (y m b)).trans hclose.le)
  let A := finiteComplexSetMean (S m) (fun a => F (x m a))
  let B := finiteComplexSetMean (T m) (fun b => F (y m b))
  let C := finiteComplexSetMean (S m) (fun a => G (x m a))
  let D := finiteComplexSetMean (T m) (fun b => G (y m b))
  have hid : A-B=(A-C)+(C-D)-(B-D) := by ring
  have ht : ‖A-B‖ ≤ ‖A-C‖+‖C-D‖+‖B-D‖ := by
    rw [hid]
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  change ‖A-C‖ ≤ ε/4 at hS
  change ‖B-D‖ ≤ ε/4 at hT
  change ‖C-D‖ < ε/4 at hm
  change ‖A-B‖ < ε
  linarith

end Hindman168
