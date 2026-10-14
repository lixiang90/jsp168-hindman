import Hindman168.IteratedEmpiricalEquality
import Hindman168.ContinuousEmpiricalComparison
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual projected empirical comparison and length-first local limits imply
invariance of the genuine projected probability measure. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Topology

theorem local_empirical_projected_measure_invariant {X Y ι : Type*}
    [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (S : ℝ → ℕ → Finset ι) (x : ℕ → ι → X)
    (hlocal : ∀ F : C(X,ℂ), ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧
      ∀ α : ℝ, 0 < α → α < r → ∀ᶠ m in atTop,
        ‖finiteComplexSetMean (S α m) (fun a => F (x m a)) - ∫ z, F z ∂μ‖ < ε)
    (π : C(X,Y)) (T : Y → Y) (hT : Continuous T)
    (hcompare : ∀ α : ℝ, 0 < α → ∀ F : C(Y,ℂ), ∀ K : NNReal, LipschitzWith K F →
      Tendsto (fun m => finiteComplexSetMean (S α m) (fun a => F (T (π (x m a)))) -
        finiteComplexSetMean (S α m) (fun a => F (π (x m a)))) atTop (𝓝 0)) :
    Measure.map T (Measure.map π μ) = Measure.map π μ := by
  have hcont α hα : ∀ F : C(Y,ℂ),
      Tendsto (fun m => finiteComplexSetMean (S α m) (fun a => F (T (π (x m a)))) -
        finiteComplexSetMean (S α m) (fun a => F (π (x m a)))) atTop (𝓝 0) :=
    continuous_empirical_comparison_of_lipschitz (S α) (S α)
      (fun m a => T (π (x m a))) (fun m a => π (x m a)) (hcompare α hα)
  have hread (F : C(Y,ℂ)) : (∫ z, F (T (π z)) ∂μ) = ∫ z, F (π z) ∂μ := by
    let A : C(X,ℂ) := (F.comp ⟨T,hT⟩).comp π
    let B : C(X,ℂ) := F.comp π
    exact iterated_empirical_limits_equal _ _ _ _ (hlocal A) (hlocal B)
      (fun α hα => hcont α hα F)
  letI : IsProbabilityMeasure (Measure.map π μ) := Measure.isProbabilityMeasure_map π.continuous.measurable.aemeasurable
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let F : C(Y,ℂ) := ⟨fun y => (f y : ℂ),Complex.continuous_ofReal.comp f.continuous⟩
  have he := hread F
  change (∫ z, (f (T (π z)) : ℂ) ∂μ) = ∫ z, (f (π z) : ℂ) ∂μ at he
  rw [integral_complex_ofReal,integral_complex_ofReal] at he
  have hr := Complex.ofReal_injective he
  rw [integral_map hT.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  have hm := integral_map (μ := μ) π.continuous.measurable.aemeasurable
    (f.continuous.comp hT).aestronglyMeasurable
  simp only [Function.comp_apply] at hm
  rw [hm, integral_map π.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact hr

end Hindman168
