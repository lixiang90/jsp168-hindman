import Hindman168.NativeRationalCompactTerminalPairSamples
import Hindman168.NativeRationalTerminalReducedPairDiscrepancy

/-! Exact original Fourier derivative mean equals actual constructed weighted degree-reduced polynomial canonical discrepancy. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff Classical
universe u

theorem native_rational_compact_reduced_polynomial_discrepancy {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (h : ℤ) (a : Finset ℤ) :
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
      nativeNilmanifoldFiniteDiscrepancy (nativeRationalDegreeReducedData D L) a
        (fun n => nativeMvPolynomialOrbit (nativeRationalDegreeReducedData D L)
          (nativeRationalCompactReducedPolynomial D L p hp h) (fun _ => n))
        (nativeRationalTerminalReducedPairObservable D L k (nativeRationalShiftRepresentative D p h)
          (nativeBasepointObservable D (nativeRationalBasepointRepresentative D p) H)) =
      finiteComplexSetMean a (fun n =>
        nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n+h)) *
          star (nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n)))) := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalDegreeReducedData D L).metric
  letI : TopologicalSpace ((nativeRationalDegreeReducedData D L).G ⧸ (nativeRationalDegreeReducedData D L).Γ) :=
    (nativeRationalDegreeReducedData D L).metric.toUniformSpace.toTopologicalSpace
  intro H
  have he : (fun n : ℤ => nativeMvPolynomialOrbit (nativeRationalDegreeReducedData D L)
      (nativeRationalCompactReducedPolynomial D L p hp h) (fun _ => n)) =
      (fun n => nativeRationalTerminalFactorMap (nativeRationalRelativeData D L 1)
        (nativeRelativeRationalLieFiltration D L) ((nativeRationalCompactNormalizedIntegerPair D L p hp h n) :
          (nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ)) := by
    funext n
    exact native_rational_compact_reduced_polynomial_sample D L p hp h n
  rw [he]
  exact (native_rational_terminal_reduced_pair_sample_discrepancy D L hdeg k hk
    (nativeRationalShiftRepresentative D p h) a
    (fun n => ((nativeRationalCompactNormalizedIntegerPair D L p hp h n) :
      (nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ))
    (nativeBasepointObservable D (nativeRationalBasepointRepresentative D p) H)).trans
      (native_rational_compact_terminal_pair_original_mean D L p hp k h a H)

end Hindman168
