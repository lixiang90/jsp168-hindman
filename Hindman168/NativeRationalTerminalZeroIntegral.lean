import Hindman168.NativeRationalTerminalFourierProjection
import Mathlib.MeasureTheory.Integral.Prod

/-! ACTUAL original terminal zero-mode averaging preserves ORIGINAL
canonical Haar mean by genuine Fubini and original action invariance. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_zero_projection_integral {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ H : C(D.G ⧸ D.Γ,ℂ),
      (∫ q, nativeRationalTerminalFourierProjection D L 0 H q ∂nativeNilmanifoldQuotientProbability D) =
        ∫ q, H q ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI := native_nilmanifold_quotient_probability_isProbability D
  intro H
  let ν : Measure (UnitAddTorus (nativeRationalTerminalIndex D L)) :=
    Measure.pi (fun _ : nativeRationalTerminalIndex D L => AddCircle.haarAddCircle)
  have hc : Continuous (fun p : (D.G ⧸ D.Γ) × UnitAddTorus (nativeRationalTerminalIndex D L) =>
      H (nativeRationalTerminalAction D L p.2 p.1)) :=
    H.continuous.comp ((native_rational_terminal_action_continuous D L).comp
      (continuous_snd.prodMk continuous_fst))
  have hi : Integrable (Function.uncurry (fun q a => H (nativeRationalTerminalAction D L a q)))
      ((nativeNilmanifoldQuotientProbability D).prod ν) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [native_rational_terminal_fourier_projection_apply,neg_zero,UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply,one_mul]
  rw [integral_integral_swap hi]
  simp only [native_rational_terminal_action_integral]
  simp

end Hindman168
