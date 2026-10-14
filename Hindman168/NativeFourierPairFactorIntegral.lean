import Hindman168.NativeDiagonalFactorProbability
import Hindman168.NativeFourierPairIntegral
import Hindman168.NativeFourierPairPolynomial

/-! ACTUAL diagonal-factor probability has genuine same-frequency pair
means; nonzero frequencies have mean ZERO and ORIGINAL derivative samples. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] diagonal_center_normal

theorem native_fourier_pair_factor_integral {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
    letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      (∫ y, nativeFourierPairFactor D k F y ∂nativeDiagonalFactorProbability D) =
        ∫ q, nativeFourierPairObservable D k F q ∂nativeNilmanifoldQuotientProbability (nativeNilmanifoldProduct D D) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
  letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [native_diagonal_factor_probability_integral]
  simp only [native_fourier_pair_factor_apply]

theorem native_fourier_pair_factor_nonzero_mean {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) (hk : k ≠ 0) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
    letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ), (∫ y, nativeFourierPairFactor D k F y ∂nativeDiagonalFactorProbability D) = 0 := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
  letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [native_fourier_pair_factor_integral,native_fourier_pair_nonzero_canonical_mean D k hk]

theorem native_fourier_pair_factor_derivative_discrepancy {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (h : σ → ℤ)
    (a : Finset (σ → ℤ)) (k : nativeNilmanifoldCenterIndex D → ℤ) (hk : k ≠ 0) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
    letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      finiteComplexSetMean a (fun x => nativeFourierPairFactor D k F (nativeDiagonalFactorMap D
        (nativeMvPolynomialOrbit (nativeNilmanifoldProduct D D) (nativePairShiftPolynomial D p h) x))) -
        (∫ y, nativeFourierPairFactor D k F y ∂nativeDiagonalFactorProbability D) =
      finiteComplexSetMean a (fun x => nativeCentralFourierProjection D k F (nativeMvPolynomialOrbit D p (x+h)) *
        star (nativeCentralFourierProjection D k F (nativeMvPolynomialOrbit D p x))) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
  letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [native_fourier_pair_factor_polynomial_mean,native_fourier_pair_factor_nonzero_mean D k hk,sub_zero]

end Hindman168
