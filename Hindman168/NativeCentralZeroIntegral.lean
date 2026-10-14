import Hindman168.NativeCentralFactorProbability
import Mathlib.MeasureTheory.Integral.Prod

/-! True Fubini/translation invariance proves zero-mode averaging preserves
the ORIGINAL Haar mean; it is not an assumed fiber disintegration. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_central_zero_projection_integral {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      (∫ q, nativeCentralFourierProjection D 0 F q ∂nativeNilmanifoldQuotientProbability D) =
        ∫ q, F q ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI := native_nilmanifold_quotient_probability_isProbability D
  intro F
  let ν : Measure (UnitAddTorus (nativeNilmanifoldCenterIndex D)) :=
    Measure.pi (fun _ : nativeNilmanifoldCenterIndex D => AddCircle.haarAddCircle)
  have hc : Continuous (fun p : (D.G ⧸ D.Γ) × UnitAddTorus (nativeNilmanifoldCenterIndex D) =>
      F (nativeNilmanifoldCentralAction D p.2 p.1)) :=
    F.continuous.comp ((native_nilmanifold_central_action_continuous D).comp
      (continuous_snd.prodMk continuous_fst))
  have hi : Integrable (Function.uncurry (fun q a => F (nativeNilmanifoldCentralAction D a q)))
      ((nativeNilmanifoldQuotientProbability D).prod ν) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [native_central_fourier_projection_apply, neg_zero, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_mul]
  rw [integral_integral_swap hi]
  simp only [native_nilmanifold_central_action_integral]
  simp

theorem native_central_zero_factor_original_integral {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      (∫ y, nativeCentralZeroObservable D F y ∂nativeCentralFactorProbability D) =
        ∫ q, F q ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [native_central_factor_zero_integral, native_central_zero_projection_integral]

end Hindman168
