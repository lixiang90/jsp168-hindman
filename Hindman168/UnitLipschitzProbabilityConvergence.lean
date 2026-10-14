import Hindman168.BoundedLipschitzNormalization
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Complex unit Lipschitz testing determines weak convergence of probabilities
on a compact metric space. Scaling is fixed per test, before the sequence limit. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Topology

theorem unit_lipschitz_probability_tendsto {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (ht : ∀ J ∈ unitLipschitzObservables X,
      Tendsto (fun n => ∫ x, J x ∂(μs n)) atTop (𝓝 (∫ x, J x ∂μ))) :
    Tendsto μs atTop (𝓝 μ) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f _ hf
  obtain ⟨K,hK⟩ := hf
  let F : C(X,ℂ) := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp hK.continuous⟩
  let R : ℝ := ‖F‖ + (K : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hFR : ‖F‖ ≤ R := by dsimp [R]; linarith [K.coe_nonneg]
  have hKR : (K : ℝ) ≤ R := by dsimp [R]; linarith [norm_nonneg F]
  have hFK : LipschitzWith (Real.toNNReal (K : ℝ)) F := by
    simpa only [Real.toNNReal_coe, one_mul, F, ContinuousMap.coe_mk, Function.comp_def]
      using Complex.isometry_ofReal.lipschitz.comp hK
  have hunit := bounded_lipschitz_normalization X F ‖F‖ K R hR hFR hKR F.norm_coe_le_norm hFK
  have htF := (ht _ hunit).const_mul (R : ℂ)
  have hRz : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have he (ν : Measure X) :
      (R : ℂ) * (∫ x, (((R : ℂ)⁻¹ • F) : C(X,ℂ)) x ∂ν) = ∫ x, F x ∂ν := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul,
      ← mul_assoc, mul_inv_cancel₀ hRz, one_mul]
  simp only [he] at htF
  have hr := Complex.continuous_re.continuousAt.tendsto.comp htF
  simpa only [F, ContinuousMap.coe_mk, integral_complex_ofReal, Complex.ofReal_re,
    Function.comp_def] using hr

end Hindman168
