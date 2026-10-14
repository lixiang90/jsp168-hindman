import Hindman168.NativeConstantProductPerturbation
import Hindman168.NativeBasepointShiftPolynomial
import Hindman168.RoughVectorCoefficientEvaluationEquality

/-! ACTUAL first-minus-second logarithmic polynomial of the original
normalized relative pair has weight ONE in SAME original Lie filtration.
The exact first-coordinate polynomial and original coefficients are retained. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeBasepointPairDifferencePolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (r t : D.G) (h : ℤ) : RoughVectorMvPolynomial Unit D.E :=
  let q := nativeBasepointPolynomial D p r
  let qs := roughVectorMvAffineSubstitution (fun _ => (h : ℝ)) (fun _ => 1) q
  let v := ((-h : ℤ) : ℝ) • roughVectorMvEval (E := D.E) q (fun _ => 1)
  let u := nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) t
  let a := roughNativeProductMvPolynomial (I := D.I) (G := D.G) qs (roughVectorMvConstant v)
  let b := roughNativeProductMvPolynomial (I := D.I) (G := D.G) (roughVectorMvConstant (-u)) a
  ((roughVectorMvDifference (fun _ => (h : ℝ)) q ++ nativeRightConstantPerturbation D qs v) ++
    nativeLeftConstantPerturbation D a (-u)) ++ nativeRightConstantPerturbation D b u

theorem native_basepoint_pair_difference_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (r t : D.G) (h : ℤ) (x : Unit → ℝ) :
    roughVectorMvEval (E := D.E) (nativeBasepointPairDifferencePolynomial D p r t h) x =
      roughVectorMvEval (E := D.E) (nativeBasepointShiftPolynomial D p r t h) x-
      roughVectorMvEval (E := D.E) (nativeBasepointPolynomial D p r) x := by
  let q := nativeBasepointPolynomial D p r
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
      roughVectorMvEval (E := D.E) (nativeBasepointShiftPolynomial D p r t h) x := by
    rw [native_basepoint_shift_polynomial_eval]
    simp only [c,b,a,u,v,qs,q,nativeBasepointShiftRawPolynomial,
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

theorem native_basepoint_pair_difference_weighted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
      (nativeBasepointPairDifferencePolynomial D p r t h) 1 := by
  let q := nativeBasepointPolynomial D p r
  let qs := roughVectorMvAffineSubstitution (fun _ => (h : ℝ)) (fun _ => 1) q
  let v := ((-h : ℤ) : ℝ) • roughVectorMvEval (E := D.E) q (fun _ => 1)
  let u := nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) t
  let a := roughNativeProductMvPolynomial (I := D.I) (G := D.G) qs (roughVectorMvConstant v)
  let b := roughNativeProductMvPolynomial (I := D.I) (G := D.G) (roughVectorMvConstant (-u)) a
  have hq := native_basepoint_polynomial_weighted D d hd p hp r
  have hqs := rough_vector_weighted_affine _ (rough_native_stretched_lie_antitone d hd)
    (fun _ : Unit => (h : ℝ)) (fun _ : Unit => 1) hq
  have hc : ∀ z : D.E, RoughVectorMvWeightedDegree
      (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) (roughVectorMvConstant (σ := Unit) z) 0 := by
    intro z
    apply rough_vector_constant_weighted
    rw [rough_native_stretched_lie_initial d hd 0 (Nat.zero_le d)]
    exact Submodule.mem_top
  have ha := rough_native_product_polynomial_weighted d hd hqs (hc v)
  have hb := rough_native_product_polynomial_weighted d hd (hc (-u)) ha
  exact rough_vector_weighted_append _ (rough_vector_weighted_append _
    (rough_vector_weighted_append _
      (rough_vector_weighted_difference _ (rough_native_stretched_lie_antitone d hd) (fun _ : Unit => (h : ℝ)) hq)
      (native_constant_product_perturbation_weighted D d hd qs hqs v).1)
    (native_constant_product_perturbation_weighted D d hd a ha (-u)).2)
    (native_constant_product_perturbation_weighted D d hd b hb u).1

end Hindman168
