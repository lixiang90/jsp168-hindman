import Hindman168.NativeRationalDifferenceExtension
import Hindman168.NativeRationalCompactUnivariateScalars
import Hindman168.NativeRationalCompactHorizontalPolynomial
import Hindman168.NativeLinearStepHorizontal
import Hindman168.UnitMvNonlinearPartCoefficients

/-! TRUE native F_2 Q and the ACTUAL raw removed Q_F have EXACTLY the same
EVERY higher monomial/binomial coefficient. Complete polynomials differ
in affine terms; no false full-polynomial equality is asserted. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_nonlinear_scalar_extension_projection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0)=0) :
    nativeRationalNonlinearScalar D L p hp h0 χ =
      roughVectorMvProjection (nativeRationalDifferenceExtension D L χ).toLinearMap
        (nativeLinearStepPolynomial D p (nativeIntegerLogPolynomialSequence D p 1)) := by
  have he : (nativeRationalDifferenceExtension D L χ).toLinearMap.comp (L.layer 2).subtype =
      (nativeRationalRelativeDifferenceCharacter D L χ).toLinearMap := by
    ext v
    exact native_rational_difference_extension_restriction D L χ v
  rw [nativeRationalNonlinearScalar,nativeRationalNonlinearPolynomial,← he]
  exact rough_vector_submodule_polynomial_projection _ _ _ _

theorem native_rational_compact_nonlinear_original_high_coefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (j : ℕ) (hj : 2 ≤ j) :
    (nativeRationalCompactNonlinearScalar D L p hp χ).coeff j =
      (scalarUnitPolynomial (roughVectorMvProjection (nativeRationalDifferenceExtension D L χ).toLinearMap p)).coeff j := by
  have hF := native_rational_difference_extension_kills_commutator D L χ hχ hzero
  have hJ0 : (0 : Unit →₀ ℕ) ≠ Finsupp.single () j := by
    intro he
    have hz : 0=j := by simpa using congrArg (fun J : Unit →₀ ℕ => J ()) he
    omega
  have hJ1 : (Finsupp.single () 1 : Unit →₀ ℕ) ≠ Finsupp.single () j := by
    intro he
    have hz : 1=j := by simpa using congrArg (fun J : Unit →₀ ℕ => J ()) he
    omega
  rw [nativeRationalCompactNonlinearScalar,scalar_unit_polynomial_coefficient,
    native_rational_nonlinear_scalar_extension_projection,
    native_linear_step_horizontal_non_linear_coefficient D _ _ _ hF _ hJ1,
    native_rational_compact_horizontal_polynomial D p _ hF,scalar_unit_polynomial_coefficient]
  simp only [MvPolynomial.coeff_sub,MvPolynomial.coeff_C,MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X,if_neg hJ0,if_neg hJ1,mul_zero,sub_zero]

theorem native_rational_raw_nonlinear_high_coefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (j : ℕ) (hj : 2 ≤ j) :
    (scalarUnitPolynomial (unitMvNonlinearPart (roughVectorMvProjection (nativeRationalDifferenceExtension D L χ).toLinearMap p))).coeff j =
      (nativeRationalCompactNonlinearScalar D L p hp χ).coeff j :=
  (unit_mv_nonlinear_part_high_coefficient _ j hj).trans
    (native_rational_compact_nonlinear_original_high_coefficient D L χ hχ hzero p hp j hj).symm

theorem native_rational_raw_nonlinear_high_binomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (j : ℕ) (hj : 2 ≤ j) :
    scalarPolynomialBinomialCoefficient
      (scalarUnitPolynomial (unitMvNonlinearPart (roughVectorMvProjection (nativeRationalDifferenceExtension D L χ).toLinearMap p))) ℓ j =
      scalarPolynomialBinomialCoefficient (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ j :=
  scalar_binomial_high_coefficient_congr _ _ (native_rational_raw_nonlinear_high_coefficient D L χ hχ hzero p hp) ℓ j hj

end Hindman168
