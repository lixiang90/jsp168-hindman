import Hindman168.NativeRationalWeightedIntegerPair
import Hindman168.NativeLieRationalPowerMembership

/-! The ACTUAL first coordinate logarithmic polynomial of the normalized
shifted pair, for arbitrary actual weighted source coefficients. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalWeightedShiftPolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (t : D.G) (h : ℤ) :
    RoughVectorMvPolynomial Unit D.E :=
  roughNativeProductMvPolynomial (I := D.I) (G := D.G)
    (roughVectorMvConstant (-nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) t))
    (roughNativeProductMvPolynomial (I := D.I) (G := D.G)
      (roughVectorMvAffineSubstitution (fun _ => (h : ℝ)) (fun _ => 1) p)
      (roughNativeProductMvPolynomial (I := D.I) (G := D.G)
        (roughVectorMvConstant (((-h : ℤ) : ℝ) • roughVectorMvEval (E := D.E) p (fun _ => 1)))
        (roughVectorMvConstant (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) t))))

theorem native_rational_weighted_shift_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (t : D.G) (h : ℤ) (x : Unit → ℝ) :
    roughVectorMvEval (E := D.E) (nativeRationalWeightedShiftPolynomial D p t h) x =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (t⁻¹ * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) p (fun j => x j+(h : ℝ))) *
          (nativeIntegerLogPolynomialSequence D p 1 ^ h)⁻¹ * t) := by
  have hn : ∀ v : D.E, nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (-v) =
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v)⁻¹ :=
    nativeLieExponential_neg (E := D.E) (I := D.I) (G := D.G)
  have hPow : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (((-h : ℤ) : ℝ) • roughVectorMvEval (E := D.E) p (fun _ => 1)) =
      (nativeIntegerLogPolynomialSequence D p 1 ^ h)⁻¹ := by
    rw [nativeLieExponential_int_smul,zpow_neg]
    congr 2
    simp only [nativeIntegerLogPolynomialSequence,Int.cast_one]
  simp only [nativeRationalWeightedShiftPolynomial,roughNativeProductMvPolynomial_eval,
    rough_vector_constant_eval,nativeLieExponential_globalLogarithm,hn,hPow,roughVectorMvAffineSubstitution_eval]
  simp only [one_mul,add_comm (h : ℝ),mul_assoc]

theorem native_rational_weighted_shift_polynomial_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {p : RoughVectorMvPolynomial Unit D.E} (hp : RoughVectorMvWeightedDegree F.layer p 0) (t : D.G) (h : ℤ) :
    RoughVectorMvWeightedDegree F.layer (nativeRationalWeightedShiftPolynomial D p t h) 0 := by
  unfold nativeRationalWeightedShiftPolynomial
  apply native_rational_product_polynomial_weighted D F (native_rational_constant_zero_weighted D F _)
  apply native_rational_product_polynomial_weighted D F (rough_vector_weighted_affine F.layer F.antitone _ _ hp)
  exact native_rational_product_polynomial_weighted D F
    (native_rational_constant_zero_weighted D F _) (native_rational_constant_zero_weighted D F _)

end Hindman168
