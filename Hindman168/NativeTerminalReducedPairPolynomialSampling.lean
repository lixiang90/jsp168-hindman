import Hindman168.NativeTerminalReducedPairUnitDetection

/-! SAME ACTUAL relative polynomial samples project to SAME reduced
native orbit in actual terminal-pair discrepancy and finite-unit detection.
Original normalized shifted polynomial membership remains a separate task. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_terminal_reduced_pair_polynomial_discrepancy {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (hdeg : 2 ≤ s*d)
    (k : nativeOriginalTerminalIndex D d → ℤ) (hk : k ≠ 0) (g : D.G)
    (a : Finset (σ → ℤ)) (p : RoughVectorMvPolynomial σ (nativeRelativeSquareData D d hd 1).E) :
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
        (nativeMvPolynomialOrbit (nativeRelativeReducedData D d hd) (nativeRelativeReductionPolynomial D d hd p))
        (nativeTerminalReducedMetricObservable D d hd k g F) =
      finiteComplexSetMean a (fun x => nativeTerminalRelativePairObservable D d hd k g F
        (nativeMvPolynomialOrbit (nativeRelativeSquareData D d hd 1) p x)) := by
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
  have he : (fun x : σ → ℤ => nativeRelativeReductionFactorMap D d hd
      (nativeMvPolynomialOrbit (nativeRelativeSquareData D d hd 1) p x)) =
      nativeMvPolynomialOrbit (nativeRelativeReducedData D d hd) (nativeRelativeReductionPolynomial D d hd p) := by
    funext x
    exact native_relative_reduction_polynomial_orbit D d hd p x
  exact (congrArg (fun f : (σ → ℤ) → (nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ =>
    nativeNilmanifoldFiniteDiscrepancy (nativeRelativeReducedData D d hd) a f
      (nativeTerminalReducedMetricObservable D d hd k g F)) he).symm.trans
    (native_terminal_reduced_pair_sample_discrepancy D d hd hdeg k hk g a
      (nativeMvPolynomialOrbit (nativeRelativeSquareData D d hd 1) p) F)

end Hindman168
