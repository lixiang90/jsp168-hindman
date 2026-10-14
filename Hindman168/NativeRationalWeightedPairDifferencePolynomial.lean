import Hindman168.NativeConstantProductPerturbation
import Hindman168.NativeRationalWeightedShiftPolynomial
import Hindman168.RoughVectorCoefficientEvaluationEquality

/-! ACTUAL first-minus-second logarithmic polynomial of the original
normalized relative pair has weight ONE in SAME original Lie filtration.
The exact first-coordinate polynomial and original coefficients are retained. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalWeightedPairDifferencePolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (t : D.G) (h : ℤ) : RoughVectorMvPolynomial Unit D.E :=
  let q := p
  let qs := roughVectorMvAffineSubstitution (fun _ => (h : ℝ)) (fun _ => 1) q
  let v := ((-h : ℤ) : ℝ) • roughVectorMvEval (E := D.E) q (fun _ => 1)
  let u := nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) t
  let a := roughNativeProductMvPolynomial (I := D.I) (G := D.G) qs (roughVectorMvConstant v)
  let b := roughNativeProductMvPolynomial (I := D.I) (G := D.G) (roughVectorMvConstant (-u)) a
  ((roughVectorMvDifference (fun _ => (h : ℝ)) q ++ nativeRightConstantPerturbation D qs v) ++
    nativeLeftConstantPerturbation D a (-u)) ++ nativeRightConstantPerturbation D b u

theorem native_rational_weighted_pair_difference_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (t : D.G) (h : ℤ) (x : Unit → ℝ) :
    roughVectorMvEval (E := D.E) (nativeRationalWeightedPairDifferencePolynomial D p t h) x =
      roughVectorMvEval (E := D.E) (nativeRationalWeightedShiftPolynomial D p t h) x-
      roughVectorMvEval (E := D.E) (p) x := by
  let q := p
  let qs := roughVectorMvAffineSubstitution (fun _ => (h : ℝ)) (fun _ => 1) q
  let v := ((-h : ℤ) : ℝ) • roughVectorMvEval (E := D.E) q (fun _ => 1)
  let u := nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) t
  let a := roughNativeProductMvPolynomial (I := D.I) (G := D.G) qs (roughVectorMvConstant v)
  let b := roughNativeProductMvPolynomial (I := D.I) (G := D.G) (roughVectorMvConstant (-u)) a
  let c := roughNativeProductMvPolynomial (I := D.I) (G := D.G) b (roughVectorMvConstant u)
  have hShift : roughVectorMvEval (E := D.E) (roughVectorMvDifference (fun _ => (h : ℝ)) q) x =
      roughVectorMvEval (E := D.E) qs x-roughVectorMvEval (E := D.E) q x := by
    rw [rough_vector_difference_eval]
    simp only [qs,roughVectorMvAffineSubstitution_eval,one_mul,add_comm (h : ℝ)]
  have hC : roughVectorMvEval (E := D.E) c x =
      roughVectorMvEval (E := D.E) (nativeRationalWeightedShiftPolynomial D p t h) x := by
    simp only [c,b,a,u,v,qs,q,nativeRationalWeightedShiftPolynomial,
      roughNativeProductMvPolynomial_eval,rough_vector_constant_eval,nativeLieExponential_globalLogarithm,mul_assoc]
  change roughVectorMvEval (E := D.E)
    (((roughVectorMvDifference (fun _ => (h : ℝ)) q ++ nativeRightConstantPerturbation D qs v) ++
      nativeLeftConstantPerturbation D a (-u)) ++ nativeRightConstantPerturbation D b u) x = _
  simp only [roughVectorMvEval_append]
  rw [hShift,native_right_constant_perturbation_eval D qs v x,
    native_left_constant_perturbation_eval D a (-u) x,native_right_constant_perturbation_eval D b u x]
  change ((roughVectorMvEval qs x-roughVectorMvEval q x)+(roughVectorMvEval a x-roughVectorMvEval qs x))+
    (roughVectorMvEval b x-roughVectorMvEval a x)+(roughVectorMvEval c x-roughVectorMvEval b x) = _
  rw [hC]
  abel

theorem native_rational_weighted_pair_difference_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (t : D.G) (h : ℤ) :
    RoughVectorMvWeightedDegree F.layer (nativeRationalWeightedPairDifferencePolynomial D p t h) 1 := by
  let qs := roughVectorMvAffineSubstitution (fun _ => (h : ℝ)) (fun _ => 1) p
  let v := ((-h : ℤ) : ℝ) • roughVectorMvEval (E := D.E) p (fun _ => 1)
  let u := nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) t
  let a := roughNativeProductMvPolynomial (I := D.I) (G := D.G) qs (roughVectorMvConstant v)
  let b := roughNativeProductMvPolynomial (I := D.I) (G := D.G) (roughVectorMvConstant (-u)) a
  have hqs := rough_vector_weighted_affine F.layer F.antitone (fun _ : Unit => (h : ℝ)) (fun _ : Unit => 1) hp
  have ha := native_rational_product_polynomial_weighted D F hqs (native_rational_constant_zero_weighted D F v)
  have hb := native_rational_product_polynomial_weighted D F (native_rational_constant_zero_weighted D F (-u)) ha
  exact rough_vector_weighted_append _ (rough_vector_weighted_append _
    (rough_vector_weighted_append _
      (rough_vector_weighted_difference F.layer F.antitone (fun _ : Unit => (h : ℝ)) hp)
      (native_rational_constant_product_perturbation_weighted D F qs hqs v).1)
    (native_rational_constant_product_perturbation_weighted D F a ha (-u)).2)
    (native_rational_constant_product_perturbation_weighted D F b hb u).1

end Hindman168
