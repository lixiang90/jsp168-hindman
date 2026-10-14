import Hindman168.NativeRationalWeightedShiftPolynomial
import Hindman168.NativeRationalRelativeExponentialLogarithm
import Hindman168.RoughVectorCoefficientSubmodule

/-! The original normalized shifted pair has an ACTUAL ambient product
logarithmic polynomial. Genuine original relative group/log compatibility
and algebraic natural-grid coefficient recovery put ALL its aggregated
coefficients in the SAME actual relative native Lie model. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalWeightedAmbientPairPolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (t : D.G) (h : ℤ) : RoughVectorMvPolynomial Unit (D.E × D.E) :=
  roughVectorMvLinearMap (LinearMap.inl ℝ D.E D.E) (nativeRationalWeightedShiftPolynomial D p t h) ++
    roughVectorMvLinearMap (LinearMap.inr ℝ D.E D.E) (p)

theorem native_rational_weighted_ambient_pair_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (t : D.G) (h : ℤ) (x : Unit → ℝ) :
    roughVectorMvEval (E := D.E × D.E) (nativeRationalWeightedAmbientPairPolynomial D p t h) x =
      (roughVectorMvEval (E := D.E) (nativeRationalWeightedShiftPolynomial D p t h) x,
        roughVectorMvEval (E := D.E) (p) x) := by
  simp only [nativeRationalWeightedAmbientPairPolynomial,roughVectorMvEval_append,roughVectorMvLinearMap_eval,
    LinearMap.inl_apply,LinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add]

theorem native_rational_weighted_ambient_pair_integer_log {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (t : D.G) (h n : ℤ) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    roughVectorMvEval (E := D.E × D.E) (nativeRationalWeightedAmbientPairPolynomial D p t h) (fun _ => (n : ℝ)) =
      nativeLieGlobalLogarithm (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
        (nativeRationalRelativeGroupInclusion D F 1 (nativeRationalWeightedIntegerPair D F p hp h0 t h n)) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  let P := nativeIntegerLogPolynomialSequence D (p)
  have hfirst : (roughNormalizedIntegerPair P t h n).1 = t⁻¹ * P (n+h) * (P 1 ^ h)⁻¹ * t := by
    have he := congrArg (fun z : D.G => t⁻¹*z)
      (rough_normalized_integer_pair_translated_first P t h n)
    simpa only [inv_mul_cancel_left,mul_assoc] using he
  rw [native_rational_weighted_ambient_pair_eval,native_rational_weighted_shift_eval,
    native_rational_weighted_integer_pair_inclusion,nativeProductGlobalLogarithm_eq,
    rough_normalized_integer_pair_second]
  apply Prod.ext
  · change nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (t⁻¹ * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) (p) (fun _ => (n : ℝ)+(h : ℝ))) *
        (P 1 ^ h)⁻¹ * t) = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (roughNormalizedIntegerPair P t h n).1
    rw [hfirst]
    simp only [P,nativeIntegerLogPolynomialSequence,Int.cast_add]
  · exact (nativeLieGlobalLogarithm_exponential (E := D.E) (I := D.I) (G := D.G) _).symm

theorem native_rational_weighted_ambient_pair_nat_mem {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (t : D.G) (h : ℤ) (x : Unit → ℕ) :
    roughVectorMvEval (E := D.E × D.E) (nativeRationalWeightedAmbientPairPolynomial D p t h) (fun j => (x j : ℝ)) ∈
      nativeLieSubalgebraModel (nativeRationalRelativeNativeSubalgebra D F 1) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  have hx : (fun j : Unit => (x j : ℝ)) = (fun _ : Unit => ((x () : ℤ) : ℝ)) := by
    funext j
    cases j
    simp only [Int.cast_natCast]
  rw [hx,native_rational_weighted_ambient_pair_integer_log D F p hp h0 t h (x () : ℤ)]
  have he := native_rational_relative_data_logarithm D F 1
    (nativeRationalWeightedIntegerPair D F p hp h0 t h (x () : ℤ))
  rw [← he]
  exact (nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D F 1).E)
    (I := (nativeRationalRelativeData D F 1).I) (G := (nativeRationalRelativeData D F 1).G)
      (nativeRationalWeightedIntegerPair D F p hp h0 t h (x () : ℤ))).property

theorem native_rational_weighted_ambient_pair_coefficient_mem {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (t : D.G) (h : ℤ) (J : Unit →₀ ℕ) :
    roughVectorMvCoefficient (nativeRationalWeightedAmbientPairPolynomial D p t h) J ∈
      nativeLieSubalgebraModel (nativeRationalRelativeNativeSubalgebra D F 1) :=
  rough_vector_coefficient_mem_of_nat_values _ _ (native_rational_weighted_ambient_pair_nat_mem D F p hp h0 t h) J

end Hindman168
