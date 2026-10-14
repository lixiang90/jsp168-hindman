import Hindman168.NativeBasepointReducedPolynomial
import Hindman168.NativeBasepointTerminalPairSamples
import Hindman168.NativeTerminalReducedPairDiscrepancy

/-! EXACT original terminal derivative average is the genuine reduced
native canonical discrepancy on the ACTUAL constructed reduced polynomial
orbit. No source polynomial assumed already in the relative model. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_basepoint_reduced_polynomial_discrepancy {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (hdeg : 2 ≤ s*d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (γ0 γh : D.Γ)
    (hr : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p 0) = r * γ0)
    (k : nativeOriginalTerminalIndex D d → ℤ) (hk : k ≠ 0) (h : ℤ) (a : Finset ℤ)
    (ht : nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r) 1 ^ h = t * γh) :
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
        (fun n => nativeMvPolynomialOrbit (nativeRelativeReducedData D d hd)
          (nativeBasepointReducedPolynomial D d hd p hp r t h) (fun _ => n))
        (nativeTerminalReducedMetricObservable D d hd k t (nativeBasepointObservable D r F)) =
      finiteComplexSetMean a (fun n => nativeOriginalTerminalFourierProjection D d hd k F
        (nativeIntegerLogPolynomialSequence D p (n+h) : D.G ⧸ D.Γ) *
        star (nativeOriginalTerminalFourierProjection D d hd k F
          (nativeIntegerLogPolynomialSequence D p n : D.G ⧸ D.Γ))) := by
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
  have he : (fun n : ℤ => nativeMvPolynomialOrbit (nativeRelativeReducedData D d hd)
      (nativeBasepointReducedPolynomial D d hd p hp r t h) (fun _ => n)) =
      (fun n => nativeRelativeReductionFactorMap D d hd
        (nativeBasepointRelativeIntegerPair D d hd p hp r t h n :
          (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ)) := by
    funext n
    exact native_basepoint_reduced_polynomial_orbit D d hd p hp r t h n
  rw [he]
  exact (native_terminal_reduced_pair_sample_discrepancy D d hd hdeg k hk t a
    (fun n => (nativeBasepointRelativeIntegerPair D d hd p hp r t h n :
      (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ))
    (nativeBasepointObservable D r F)).trans
      (native_basepoint_terminal_pair_original_mean D d hd p hp r t γ0 γh hr k h a ht F)

end Hindman168
