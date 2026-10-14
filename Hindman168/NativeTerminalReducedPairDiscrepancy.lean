import Hindman168.NativeTerminalReducedMetricObservable
import Hindman168.NativeTerminalReducedPairMean
import Hindman168.NativeRelativeReductionPolynomial
import Hindman168.NativeNilmanifoldFiniteDiscrepancy

/-! ACTUAL reduced specified-metric canonical Haar discrepancy equals
SAME ACTUAL relative terminal pair finite average, retaining projected samples. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_terminal_reduced_pair_sample_discrepancy {s : ℕ} {α : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (hdeg : 2 ≤ s*d)
    (k : nativeOriginalTerminalIndex D d → ℤ) (hk : k ≠ 0) (g : D.G)
    (a : Finset α) (f : α → (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ) :
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
    letI : MeasurableSpace (nativeRelativeReducedData D d hd).E := borel (nativeRelativeReducedData D d hd).E
    letI : MeasurableSpace (nativeRelativeReducedData D d hd).G := borel (nativeRelativeReducedData D d hd).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRelativeReducedData D d hd).metric
    letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
      (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeNilmanifoldFiniteDiscrepancy (nativeRelativeReducedData D d hd) a
        (fun x => nativeRelativeReductionFactorMap D d hd (f x)) (nativeTerminalReducedMetricObservable D d hd k g F) =
      finiteComplexSetMean a (fun x => nativeTerminalRelativePairObservable D d hd k g F (f x)) := by
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
  letI : MeasurableSpace (nativeRelativeReducedData D d hd).E := borel (nativeRelativeReducedData D d hd).E
  letI : MeasurableSpace (nativeRelativeReducedData D d hd).G := borel (nativeRelativeReducedData D d hd).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRelativeReducedData D d hd).metric
  letI : TopologicalSpace ((nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) :=
    (nativeRelativeReducedData D d hd).metric.toUniformSpace.toTopologicalSpace
  intro F
  have he : (fun y : (nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ =>
      nativeTerminalReducedMetricObservable D d hd k g F y) =
      (fun y : (nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ =>
        nativeTerminalReducedPairObservable D d hd k g F y) := by
    funext y
    exact native_terminal_reduced_metric_observable_apply D d hd k g F y
  change finiteComplexSetMean a (fun x => nativeTerminalReducedMetricObservable D d hd k g F
    (nativeRelativeReductionFactorMap D d hd (f x))) -
    (∫ y, nativeTerminalReducedMetricObservable D d hd k g F y
      ∂nativeNilmanifoldQuotientProbability (nativeRelativeReducedData D d hd)) = _
  rw [he,native_terminal_reduced_pair_nonzero_mean D d hd hdeg k hk g,sub_zero]
  congr 1
  funext x
  exact (native_terminal_reduced_metric_observable_apply D d hd k g F _).trans
    (native_terminal_reduced_pair_observable_apply D d hd k g F (f x))

end Hindman168
