import Hindman168.NativeTerminalReducedPairObservable
import Hindman168.NativeTerminalRelativePairMean
import Hindman168.NativeRelativeReductionCanonicalProbability

/-! SAME descended translated terminal pair has EXACT relative and
reduced native canonical integrals; NONZERO frequency mean is ZERO. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_terminal_reduced_pair_canonical_integral {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
    letI : MeasurableSpace (nativeRelativeReducedData D d hd).E := borel (nativeRelativeReducedData D d hd).E
    letI : MeasurableSpace (nativeRelativeReducedData D d hd).G := borel (nativeRelativeReducedData D d hd).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      (∫ y, nativeTerminalReducedPairObservable D d hd k g F y
        ∂nativeNilmanifoldQuotientProbability (nativeRelativeReducedData D d hd)) =
      ∫ q, nativeTerminalRelativePairObservable D d hd k g F q
        ∂nativeNilmanifoldQuotientProbability (nativeRelativeSquareData D d hd 1) := by
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
  letI : MeasurableSpace (nativeRelativeReducedData D d hd).E := borel (nativeRelativeReducedData D d hd).E
  letI : MeasurableSpace (nativeRelativeReducedData D d hd).G := borel (nativeRelativeReducedData D d hd).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  have hm := native_relative_reduction_canonical_integral D d hd (nativeTerminalReducedPairObservable D d hd k g F)
  have he : (fun q : (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ =>
      nativeTerminalReducedPairObservable D d hd k g F (nativeRelativeReductionFactorMap D d hd q)) =
      (fun q : (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ =>
        nativeTerminalRelativePairObservable D d hd k g F q) := by
    funext q
    exact native_terminal_reduced_pair_observable_apply D d hd k g F q
  exact hm.trans (congrArg (fun f : ((nativeRelativeSquareData D d hd 1).G ⧸
    (nativeRelativeSquareData D d hd 1).Γ) → ℂ => ∫ q, f q
      ∂nativeNilmanifoldQuotientProbability (nativeRelativeSquareData D d hd 1)) he)

theorem native_terminal_reduced_pair_nonzero_mean {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (hdeg : 2 ≤ s*d)
    (k : nativeOriginalTerminalIndex D d → ℤ) (hk : k ≠ 0) (g : D.G) :
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
    letI : MeasurableSpace (nativeRelativeReducedData D d hd).E := borel (nativeRelativeReducedData D d hd).E
    letI : MeasurableSpace (nativeRelativeReducedData D d hd).G := borel (nativeRelativeReducedData D d hd).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      (∫ y, nativeTerminalReducedPairObservable D d hd k g F y
        ∂nativeNilmanifoldQuotientProbability (nativeRelativeReducedData D d hd)) = 0 := by
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
  letI : MeasurableSpace (nativeRelativeReducedData D d hd).E := borel (nativeRelativeReducedData D d hd).E
  letI : MeasurableSpace (nativeRelativeReducedData D d hd).G := borel (nativeRelativeReducedData D d hd).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  exact (native_terminal_reduced_pair_canonical_integral D d hd k g F).trans
    (native_terminal_relative_pair_nonzero_mean D d hd hdeg k hk g F)

end Hindman168
