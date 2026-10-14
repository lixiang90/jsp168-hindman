import Hindman168.NativeRationalTerminalFactorProbability
import Hindman168.NativeRationalTerminalZeroObservable
import Hindman168.NativeRationalTerminalZeroIntegral

/-! Actual descended zero-mode integrals use the ACTUAL terminal native
canonical Haar, with every original/metric/Borel transport input proved. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_quotient_metric_borel {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI : MeasurableSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      borel ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ)
    letI := (nativeRationalTerminalQuotientData D L).metric
    letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
    BorelSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) := by
  letI : MeasurableSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    borel ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ)
  letI := (nativeRationalTerminalQuotientData D L).metric
  letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
  exact ⟨congrArg (fun t : TopologicalSpace
    ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) =>
      @borel ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) t)
    (nativeNilmanifold_metric_topology (nativeRationalTerminalQuotientData D L))⟩

theorem native_rational_terminal_factor_zero_borel_integral {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ H : C(D.G ⧸ D.Γ,ℂ),
      (∫ y, nativeRationalTerminalZeroObservable D L H y ∂nativeRationalTerminalFactorProbability D L) =
        ∫ q, nativeRationalTerminalFourierProjection D L 0 H q ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    borel ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ)
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  letI := (nativeRationalTerminalQuotientData D L).metric
  letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    native_rational_terminal_quotient_metric_borel D L
  intro H
  have he : (∫ y, nativeRationalTerminalZeroObservable D L H y ∂nativeRationalTerminalFactorProbability D L) =
      ∫ q, nativeRationalTerminalZeroObservable D L H (nativeRationalTerminalFactorMap D L q)
        ∂nativeNilmanifoldQuotientProbability D :=
    integral_map (native_rational_terminal_factor_metric_openQuotient D L).continuous.measurable.aemeasurable
      (nativeRationalTerminalZeroObservable D L H).continuous.aestronglyMeasurable
  rw [he]
  simp only [native_rational_terminal_zero_observable_apply]

theorem native_rational_terminal_zero_canonical_projection_integral {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ H : C(D.G ⧸ D.Γ,ℂ),
      (∫ y, nativeRationalTerminalZeroObservable D L H y ∂nativeNilmanifoldQuotientProbability (nativeRationalTerminalQuotientData D L)) =
        ∫ q, nativeRationalTerminalFourierProjection D L 0 H q ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro H
  have he := native_rational_terminal_factor_zero_borel_integral D L H
  rw [native_rational_terminal_factor_canonical_probability D L] at he
  exact (native_nilmanifold_borel_probability_integral (nativeRationalTerminalQuotientData D L)
    (nativeRationalTerminalZeroObservable D L H)).symm.trans he

theorem native_rational_terminal_zero_canonical_original_integral {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ H : C(D.G ⧸ D.Γ,ℂ),
      (∫ y, nativeRationalTerminalZeroObservable D L H y ∂nativeNilmanifoldQuotientProbability (nativeRationalTerminalQuotientData D L)) =
        ∫ q, H q ∂nativeNilmanifoldQuotientProbability D := by
  intro H
  exact (native_rational_terminal_zero_canonical_projection_integral D L H).trans
    (native_rational_terminal_zero_projection_integral D L H)

end Hindman168
