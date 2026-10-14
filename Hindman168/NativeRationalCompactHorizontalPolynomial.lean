import Hindman168.NativeRationalCompactNormalizedPolynomial

/-! COMPLETE horizontal scalar polynomial and EVERY original nonconstant
coefficient modulo integers survive the ACTUAL compactly chosen normalizations.
These statements apply at each true projected IMAGE filtration stage. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_compact_horizontal_polynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (f : D.E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ f.ker) :
    roughVectorMvProjection f (nativeRationalCompactNormalizedPolynomial D p) =
      roughVectorMvProjection f p - MvPolynomial.C (f (roughVectorMvEval (E := D.E) p 0)) -
      MvPolynomial.C (f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeRationalLinearLatticePart D p))) * MvPolynomial.X () := by
  rw [nativeRationalCompactNormalizedPolynomial,native_linear_step_horizontal_projection D _ _ f hf,
    native_basepoint_horizontal_projection D p _ f hf]

theorem native_rational_compact_horizontal_nonconstant_coefficient {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (f : D.E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ f.ker)
    (hInt : ∀ g : D.Γ, ∃ z : ℤ, f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) = (z : ℝ))
    (J : Unit →₀ ℕ) (hJ : J ≠ 0) :
    ∃ z : ℤ, MvPolynomial.coeff J (roughVectorMvProjection f (nativeRationalCompactNormalizedPolynomial D p)) =
      MvPolynomial.coeff J (roughVectorMvProjection f p) + (z : ℝ) :=
  native_two_normalizations_original_nonconstant_coefficients D p _ _ f hf hInt J hJ

end Hindman168
