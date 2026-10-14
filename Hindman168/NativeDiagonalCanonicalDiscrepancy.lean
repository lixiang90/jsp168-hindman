import Hindman168.NativeDiagonalCanonicalProbability

/-! SAME original derivative samples have discrepancy against GENUINE
actual diagonal native canonical Haar, not a presumed replacement measure. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] diagonal_center_normal

theorem native_diagonal_pair_nonzero_original_canonical_mean {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) (hk : k ≠ 0) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
    letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
    letI : MeasurableSpace (nativeDiagonalQuotientData D).E := borel (nativeDiagonalQuotientData D).E
    letI : MeasurableSpace (nativeDiagonalQuotientData D).G := borel (nativeDiagonalQuotientData D).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      (∫ y, nativeFourierPairFactor D k F y ∂nativeNilmanifoldQuotientProbability (nativeDiagonalQuotientData D)) = 0 := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
  letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
  letI : MeasurableSpace (nativeDiagonalQuotientData D).E := borel (nativeDiagonalQuotientData D).E
  letI : MeasurableSpace (nativeDiagonalQuotientData D).G := borel (nativeDiagonalQuotientData D).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [← native_nilmanifold_borel_probability_integral (nativeDiagonalQuotientData D)]
  exact native_diagonal_pair_nonzero_canonical_mean D k hk F

theorem native_diagonal_original_derivative_canonical_discrepancy {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (h : σ → ℤ)
    (a : Finset (σ → ℤ)) (k : nativeNilmanifoldCenterIndex D → ℤ) (hk : k ≠ 0) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
    letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
    letI : MeasurableSpace (nativeDiagonalQuotientData D).E := borel (nativeDiagonalQuotientData D).E
    letI : MeasurableSpace (nativeDiagonalQuotientData D).G := borel (nativeDiagonalQuotientData D).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      finiteComplexSetMean a (fun x => nativeFourierPairFactor D k F (nativeDiagonalFactorMap D
        (nativeMvPolynomialOrbit (nativeNilmanifoldProduct D D) (nativePairShiftPolynomial D p h) x))) -
        (∫ y, nativeFourierPairFactor D k F y ∂nativeNilmanifoldQuotientProbability (nativeDiagonalQuotientData D)) =
      finiteComplexSetMean a (fun x => nativeCentralFourierProjection D k F (nativeMvPolynomialOrbit D p (x+h)) *
        star (nativeCentralFourierProjection D k F (nativeMvPolynomialOrbit D p x))) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
  letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
  letI : MeasurableSpace (nativeDiagonalQuotientData D).E := borel (nativeDiagonalQuotientData D).E
  letI : MeasurableSpace (nativeDiagonalQuotientData D).G := borel (nativeDiagonalQuotientData D).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [native_fourier_pair_factor_polynomial_mean,native_diagonal_pair_nonzero_original_canonical_mean D k hk,sub_zero]

end Hindman168
