import Hindman168.NativeRationalNonzeroRelativeInverse

/-! Complete degree-two nonzero RELATIVE character extraction, with no child inverse premise. The original character reconstruction and full degree-two inverse remain open. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_degree_two_nonzero_relative_inverse {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D 2)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (η : ℝ) (hη : 0 < η) :
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ A : ℝ, 0 < A ∧
      ∀ (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
        (h : ℤ) (N : ℕ), 0 < N → ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        η ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
          nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n+h)) *
            star (nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n))))‖ →
        ∃ χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ,
          RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
            (nativeRationalRelativeData D L 1).Γ χ.toLinearMap ∧ ‖χ‖ ≤ A ∧
          χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := (nativeRationalRelativeData D L 1).I)
            (nativeRationalRelativeData D L 1).Γ A ∧
          (∀ J : Unit → ℕ, 0 < (∑ i, J i) →
            (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
              (roughVectorMvProjection χ.toLinearMap (nativeRationalCompactRelativePolynomial D L p hp h)) : ℝ) :
                UnitAddCircle)‖ ≤ A) ∧
          ∀ J : Unit → ℕ, 0 < (∑ i, J i) →
            (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
              (roughVectorMvProjection χ.toLinearMap (nativeRationalCompactRelativePolynomial D L p hp h))
                2 J : ℝ) : UnitAddCircle)‖ ≤ A := by
  exact native_rational_nonzero_relative_inverse D L (by omega)
    (native_rational_weighted_inverse_degree_one (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit) k hk η hη

end Hindman168
