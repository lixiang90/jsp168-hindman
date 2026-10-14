import Hindman168.NativeRationalNonzeroRelativeInverse
import Hindman168.FiniteCoefficientScaleTransfer

/-! BOTH actual relative coefficient tables on the original scale.
The required finite degree range is explicit. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u

def NativeRationalRelativeCoefficientBounds {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h : ℤ) (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (N : ℕ) (B : ℝ) : Prop :=
    (∀ J : Unit → ℕ, 0 < (∑ i, J i) → (∑ i, J i) ≤ ℓ →
      (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
        (roughVectorMvProjection χ.toLinearMap (nativeRationalCompactRelativePolynomial D L p hp h)) : ℝ) :
          UnitAddCircle)‖ ≤ B) ∧
    ∀ J : Unit → ℕ, 0 < (∑ i, J i) → (∑ i, J i) ≤ ℓ →
      (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
        (roughVectorMvProjection χ.toLinearMap (nativeRationalCompactRelativePolynomial D L p hp h)) ℓ J :
          ℝ) : UnitAddCircle)‖ ≤ B

theorem native_rational_relative_coefficient_scale {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h : ℤ) (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (N M : ℕ)
    (τ A : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hA : 0 ≤ A)
    (hlen : τ*(N : ℝ) ≤ M)
    (hcoeff : NativeRationalRelativeCoefficientBounds D L p hp h χ M A) :
    NativeRationalRelativeCoefficientBounds D L p hp h χ N (A*(τ⁻¹)^ℓ) := by
  constructor
  · intro J hJ hdeg
    exact finite_coefficient_scale_transfer N M τ A _ ℓ (∑ i, J i) hτ hτ1 hA
      (norm_nonneg _) hlen hdeg (hcoeff.1 J hJ hdeg)
  · intro J hJ hdeg
    exact finite_coefficient_scale_transfer N M τ A _ ℓ (∑ i, J i) hτ hτ1 hA
      (norm_nonneg _) hlen hdeg (hcoeff.2 J hJ hdeg)

end Hindman168
