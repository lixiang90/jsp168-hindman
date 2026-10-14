import Hindman168.NativeDiagonalPairMetricObservable
import Hindman168.NativeDiagonalPolynomialProjection
import Hindman168.NativeNilmanifoldFiniteDiscrepancy

/-! Actual CHILD-metric/canonical-Haar discrepancy on ACTUAL projected
pair polynomial orbit equals the SAME original nonzero-frequency derivative. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] diagonal_center_normal

theorem native_diagonal_pair_metric_polynomial_discrepancy {s : ℕ} {σ : Type*}
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
    letI := (nativeDiagonalQuotientData D).metric
    letI : TopologicalSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
      (nativeDiagonalQuotientData D).metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      nativeNilmanifoldFiniteDiscrepancy (nativeDiagonalQuotientData D) a
        (nativeMvPolynomialOrbit (nativeDiagonalQuotientData D)
          (nativeDiagonalPolynomialProjection D (nativePairShiftPolynomial D p h)))
        (nativeDiagonalPairMetricObservable D k F) =
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
  letI := (nativeDiagonalQuotientData D).metric
  letI : TopologicalSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
    (nativeDiagonalQuotientData D).metric.toUniformSpace.toTopologicalSpace
  intro F
  have he : (fun y : (nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ =>
      nativeDiagonalPairMetricObservable D k F y) =
      (fun y : (nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ =>
        nativeFourierPairFactor D k F y) := by
    funext y
    exact native_diagonal_pair_metric_observable_apply D k F y
  change finiteComplexSetMean a (fun x => nativeDiagonalPairMetricObservable D k F
    (nativeMvPolynomialOrbit (nativeDiagonalQuotientData D)
      (nativeDiagonalPolynomialProjection D (nativePairShiftPolynomial D p h)) x)) -
    (∫ y, nativeDiagonalPairMetricObservable D k F y ∂nativeNilmanifoldQuotientProbability (nativeDiagonalQuotientData D)) = _
  rw [he,native_diagonal_pair_nonzero_original_canonical_mean D k hk,sub_zero]
  congr 1
  funext x
  exact (congrArg (fun y : (nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ =>
    nativeDiagonalPairMetricObservable D k F y)
      (native_diagonal_polynomial_projection_orbit D (nativePairShiftPolynomial D p h) x).symm).trans
    ((native_diagonal_pair_metric_observable_apply D k F
      (nativeDiagonalFactorMap D (nativeMvPolynomialOrbit (nativeNilmanifoldProduct D D)
        (nativePairShiftPolynomial D p h) x))).trans
      (native_fourier_pair_factor_polynomial_sample D p h x k F))

end Hindman168
