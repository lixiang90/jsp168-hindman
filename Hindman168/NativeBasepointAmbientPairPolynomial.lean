import Hindman168.NativeBasepointShiftPolynomial
import Hindman168.NativeRelativeExponentialLogarithm
import Hindman168.RoughVectorCoefficientSubmodule

/-! The original normalized shifted pair has an ACTUAL ambient product
logarithmic polynomial. Genuine original relative group/log compatibility
and algebraic natural-grid coefficient recovery put ALL its aggregated
coefficients in the SAME actual relative native Lie model. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeBasepointAmbientPairPolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (r t : D.G) (h : ℤ) : RoughVectorMvPolynomial Unit (D.E × D.E) :=
  roughVectorMvLinearMap (LinearMap.inl ℝ D.E D.E) (nativeBasepointShiftPolynomial D p r t h) ++
    roughVectorMvLinearMap (LinearMap.inr ℝ D.E D.E) (nativeBasepointPolynomial D p r)

theorem native_basepoint_ambient_pair_degree {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) : RoughVectorMvDegreeLE (nativeBasepointAmbientPairPolynomial D p r t h) (s*d) :=
  roughVectorMvDegreeLE_append
    (roughVectorMvLinearMap_degree _ (native_basepoint_shift_polynomial_degree D d hd p hp r t h))
    (roughVectorMvLinearMap_degree _ (native_basepoint_polynomial_degree D d hd p hp r))

theorem native_basepoint_ambient_pair_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (r t : D.G) (h : ℤ) (x : Unit → ℝ) :
    roughVectorMvEval (E := D.E × D.E) (nativeBasepointAmbientPairPolynomial D p r t h) x =
      (roughVectorMvEval (E := D.E) (nativeBasepointShiftPolynomial D p r t h) x,
        roughVectorMvEval (E := D.E) (nativeBasepointPolynomial D p r) x) := by
  simp only [nativeBasepointAmbientPairPolynomial,roughVectorMvEval_append,roughVectorMvLinearMap_eval,
    LinearMap.inl_apply,LinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add]

theorem native_basepoint_ambient_pair_integer_log {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h n : ℤ) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    roughVectorMvEval (E := D.E × D.E) (nativeBasepointAmbientPairPolynomial D p r t h) (fun _ => (n : ℝ)) =
      nativeLieGlobalLogarithm (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
        (nativeRelativeGroupInclusion D d hd 1 (nativeBasepointRelativeIntegerPair D d hd p hp r t h n)) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  let P := nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r)
  have hfirst : (roughNormalizedIntegerPair P t h n).1 = t⁻¹ * P (n+h) * (P 1 ^ h)⁻¹ * t := by
    have he := congrArg (fun z : D.G => t⁻¹*z)
      (rough_normalized_integer_pair_translated_first P t h n)
    simpa only [inv_mul_cancel_left,mul_assoc] using he
  rw [native_basepoint_ambient_pair_eval,native_basepoint_shift_polynomial_eval,native_basepoint_shift_raw_eval,
    native_basepoint_relative_integer_pair_inclusion,nativeProductGlobalLogarithm_eq,
    rough_normalized_integer_pair_second]
  apply Prod.ext
  · change nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (t⁻¹ * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) (nativeBasepointPolynomial D p r) (fun _ => (n : ℝ)+(h : ℝ))) *
        (P 1 ^ h)⁻¹ * t) = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (roughNormalizedIntegerPair P t h n).1
    rw [hfirst]
    simp only [P,nativeIntegerLogPolynomialSequence,Int.cast_add]
  · exact (nativeLieGlobalLogarithm_exponential (E := D.E) (I := D.I) (G := D.G) _).symm

theorem native_basepoint_ambient_pair_nat_mem {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) (x : Unit → ℕ) :
    roughVectorMvEval (E := D.E × D.E) (nativeBasepointAmbientPairPolynomial D p r t h) (fun j => (x j : ℝ)) ∈
      nativeLieSubalgebraModel (nativeRelativeSquareNativeLieAlgebra D d 1) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  have hx : (fun j : Unit => (x j : ℝ)) = (fun _ : Unit => ((x () : ℤ) : ℝ)) := by
    funext j
    cases j
    simp only [Int.cast_natCast]
  rw [hx,native_basepoint_ambient_pair_integer_log D d hd p hp r t h (x () : ℤ)]
  have he := native_relative_data_logarithm D d hd 1
    (nativeBasepointRelativeIntegerPair D d hd p hp r t h (x () : ℤ))
  rw [← he]
  exact (nativeLieGlobalLogarithm (E := (nativeRelativeSquareData D d hd 1).E)
    (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G)
      (nativeBasepointRelativeIntegerPair D d hd p hp r t h (x () : ℤ))).property

theorem native_basepoint_ambient_pair_coefficient_mem {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) (J : Unit →₀ ℕ) :
    roughVectorMvCoefficient (nativeBasepointAmbientPairPolynomial D p r t h) J ∈
      nativeLieSubalgebraModel (nativeRelativeSquareNativeLieAlgebra D d 1) :=
  rough_vector_coefficient_mem_of_nat_values _ _ (native_basepoint_ambient_pair_nat_mem D d hd p hp r t h) J

end Hindman168
