import Hindman168.NativeRationalTerminalZeroCanonicalIntegral
import Hindman168.NativeNilmanifoldFiniteDiscrepancy

/-! ORIGINAL zero-mode discrepancy equals ACTUAL terminal-quotient native
canonical discrepancy on SAME actual image samples and specified metric. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_zero_discrepancy {s ℓ : ℕ} {α : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (a : Finset α) (f : α → D.G ⧸ D.Γ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalTerminalQuotientData D L).metric
    letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
    ∀ H : C(D.G ⧸ D.Γ,ℂ),
      nativeNilmanifoldFiniteDiscrepancy D a f (nativeRationalTerminalFourierProjection D L 0 H) =
      nativeNilmanifoldFiniteDiscrepancy (nativeRationalTerminalQuotientData D L) a
        (fun x => nativeRationalTerminalFactorMap D L (f x)) (nativeRationalTerminalZeroObservable D L H) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalTerminalQuotientData D L).metric
  letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
  intro H
  change finiteComplexSetMean a (fun x => nativeRationalTerminalFourierProjection D L 0 H (f x)) -
    (∫ q, nativeRationalTerminalFourierProjection D L 0 H q ∂nativeNilmanifoldQuotientProbability D) =
    finiteComplexSetMean a (fun x => nativeRationalTerminalZeroObservable D L H (nativeRationalTerminalFactorMap D L (f x))) -
    (∫ y, nativeRationalTerminalZeroObservable D L H y
      ∂nativeNilmanifoldQuotientProbability (nativeRationalTerminalQuotientData D L))
  rw [native_rational_terminal_zero_canonical_projection_integral]
  simp only [native_rational_terminal_zero_observable_apply]

end Hindman168
