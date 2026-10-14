import Hindman168.NativeRationalFirstLayerIntegerCharacter
import Hindman168.NativeRationalCompactHorizontalPolynomial
import Hindman168.RoughVectorCoefficientSubmodule
import Hindman168.ScalarUnitPolynomial

/-! Actual functionals killing F_2 turn every true weighted source into an
affine scalar polynomial. This applies to RAW sources and compact sources. -/
namespace Hindman168
open Polynomial
open scoped Manifold ContDiff
universe u

theorem native_rational_kills_two_scalar_coefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (f : D.E →ₗ[ℝ] ℝ) (hf : L.layer 2 ≤ f.ker) (j : ℕ) (hj : 2 ≤ j) :
    (scalarUnitPolynomial (roughVectorMvProjection f p)).coeff j=0 := by
  rw [scalar_unit_polynomial_coefficient,← rough_vector_coefficient_projection]
  apply hf
  have hm := rough_vector_weighted_coefficient L.layer L.antitone hp (Finsupp.single () j)
  have he : (Finsupp.single () j).sum (fun _ n => n)=j := by simp
  rw [he,Nat.add_zero] at hm
  exact L.antitone hj hm

theorem scalar_polynomial_affine_of_higher_zero (p : ℝ[X])
    (hp : ∀ j : ℕ, 2 ≤ j → p.coeff j=0) : p=C (p.coeff 0)+C (p.coeff 1)*X := by
  ext j
  rcases j with _ | j
  · simp
  rcases j with _ | j
  · simp
  · rw [hp _ (by omega),coeff_add,coeff_C,coeff_C_mul_X]
    simp

theorem native_rational_kills_two_scalar_affine {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (f : D.E →ₗ[ℝ] ℝ) (hf : L.layer 2 ≤ f.ker) :
    let P := scalarUnitPolynomial (roughVectorMvProjection f p)
    P=C (P.coeff 0)+C (P.coeff 1)*X :=
  scalar_polynomial_affine_of_higher_zero _ (native_rational_kills_two_scalar_coefficient D L p hp f hf)

theorem native_rational_compact_kills_two_first_coefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (f : D.E →ₗ[ℝ] ℝ) (hf : L.layer 2 ≤ f.ker) :
    (scalarUnitPolynomial (roughVectorMvProjection f (nativeRationalCompactNormalizedPolynomial D p))).coeff 1 =
      nativeLieLogarithmCharacter (I := D.I) (G := D.G) f
        (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1) := by
  let P := scalarUnitPolynomial (roughVectorMvProjection f (nativeRationalCompactNormalizedPolynomial D p))
  have hP : P=C (P.coeff 0)+C (P.coeff 1)*X :=
    native_rational_kills_two_scalar_affine D L (nativeRationalCompactNormalizedPolynomial D p)
      (native_rational_compact_normalized_polynomial_weighted D L hp) f hf
  have h0 : P.coeff 0=0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    change (scalarUnitPolynomial _).eval 0=0
    rw [scalar_unit_polynomial_eval,roughVectorMvProjection_eval,
      native_rational_compact_normalized_polynomial_zero,map_zero]
  have he : P.eval 1=P.coeff 1 := by
    calc
      P.eval 1=(C (P.coeff 0)+C (P.coeff 1)*X).eval 1 := congrArg (fun Q : ℝ[X] => Q.eval 1) hP
      _=P.coeff 1 := by simp only [eval_add,eval_mul,eval_C,eval_X,h0,zero_add,mul_one]
  change P.coeff 1=_
  rw [← he]
  change (scalarUnitPolynomial _).eval 1=_
  rw [scalar_unit_polynomial_eval,roughVectorMvProjection_eval,nativeIntegerLogPolynomialSequence,
    nativeLieLogarithmCharacter_exponential,Int.cast_one]

end Hindman168
