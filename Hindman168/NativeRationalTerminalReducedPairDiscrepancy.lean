import Hindman168.NativeRationalTerminalReducedPairCompact
import Hindman168.NativeRationalTerminalReducedPairMean
import Hindman168.NativeRationalDegreeRecursion
import Hindman168.NativeNilmanifoldFiniteDiscrepancy

/-! ACTUAL reduced specified-metric canonical Haar discrepancy equals
SAME ACTUAL relative terminal pair finite average, retaining projected samples. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_reduced_pair_sample_discrepancy {s ℓ : ℕ} {α : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (g : D.G)
    (a : Finset α) (f : α → (nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) :
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalDegreeReducedData D L).metric
    letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
      (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeNilmanifoldFiniteDiscrepancy (nativeRationalDegreeReducedData D L) a
        (fun x => nativeRationalTerminalFactorMap (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L) (f x)) (nativeRationalTerminalReducedPairObservable D L k g F) =
      finiteComplexSetMean a (fun x => nativeRationalTerminalRelativePairObservable D L k g F (f x)) := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalDegreeReducedData D L).metric
  letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
  intro F
  change finiteComplexSetMean a (fun x => nativeRationalTerminalReducedPairObservable D L k g F
    (nativeRationalTerminalFactorMap (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L) (f x))) -
    (∫ y, nativeRationalTerminalReducedPairObservable D L k g F y
      ∂nativeNilmanifoldQuotientProbability (nativeRationalDegreeReducedData D L)) = _
  rw [native_rational_terminal_reduced_pair_nonzero_mean D L hdeg k hk g,sub_zero]
  congr 1
  funext x
  exact (native_rational_terminal_reduced_pair_observable_apply D L k g F (f x)).trans
    (native_rational_terminal_relative_metric_observable_apply D L k g F (f x))

end Hindman168
