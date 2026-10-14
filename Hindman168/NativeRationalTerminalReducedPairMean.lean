import Hindman168.NativeRationalTerminalReducedPairObservable
import Hindman168.NativeRationalTerminalRelativePairMean
import Hindman168.NativeRationalTerminalFactorIntegral

/-! Nonzero original terminal pairs have mean zero on the actual degree-reduced
native quotient, against its canonical Haar and in its specified metric. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_reduced_pair_nonzero_mean {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (g : D.G) :
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalDegreeReducedData D L).metric
    letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
    ∀ H : C(D.G ⧸ D.Γ,ℂ),
      (∫ q, nativeRationalTerminalReducedPairObservable D L k g H q
        ∂nativeNilmanifoldQuotientProbability (nativeRationalDegreeReducedData D L)) = 0 := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalDegreeReducedData D L).metric
  letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalRelativeData D L 1).metric
  letI : TopologicalSpace ((nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) :=
    (nativeRationalRelativeData D L 1).metric.toUniformSpace.toTopologicalSpace
  intro H
  have he := native_rational_terminal_factor_canonical_integral (nativeRationalRelativeData D L 1)
    (nativeRelativeRationalLieFiltration D L) (nativeRationalTerminalReducedPairObservable D L k g H)
  refine he.trans ?_
  calc
    _ = ∫ q, nativeRationalTerminalRelativePairObservable D L k g H q
        ∂nativeNilmanifoldQuotientProbability (nativeRationalRelativeData D L 1) := by
      apply integral_congr_ae
      filter_upwards with q
      exact (native_rational_terminal_reduced_pair_observable_apply D L k g H q).trans
        (native_rational_terminal_relative_metric_observable_apply D L k g H q)
    _ = 0 := native_rational_terminal_relative_pair_nonzero_mean D L hdeg k hk g H

end Hindman168
