import Hindman168.NativeBasepointRelativeIntegerPair
import Hindman168.NativeLieRationalPowerMembership
import Hindman168.RoughNativeProductWeighted

/-! ACTUAL original first coordinate of the normalized shifted pair has
a genuine native logarithmic coefficient polynomial. Its SAME original
stretched Lie weights are retained; no relative degree assertion is assumed. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeBasepointShiftRawPolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (r t : D.G) (h : ℤ) : RoughVectorMvPolynomial Unit D.E :=
  roughNativeProductMvPolynomial (I := D.I) (G := D.G)
    (roughVectorMvConstant (-nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) t))
    (roughNativeProductMvPolynomial (I := D.I) (G := D.G)
      (roughVectorMvAffineSubstitution (fun _ => (h : ℝ)) (fun _ => 1) (nativeBasepointPolynomial D p r))
      (roughNativeProductMvPolynomial (I := D.I) (G := D.G)
        (roughVectorMvConstant (((-h : ℤ) : ℝ) •
          roughVectorMvEval (E := D.E) (nativeBasepointPolynomial D p r) (fun _ => 1)))
        (roughVectorMvConstant (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) t))))

theorem native_basepoint_shift_raw_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (r t : D.G) (h : ℤ) (x : Unit → ℝ) :
    roughVectorMvEval (E := D.E) (nativeBasepointShiftRawPolynomial D p r t h) x =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (t⁻¹ * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) (nativeBasepointPolynomial D p r) (fun j => x j+(h : ℝ))) *
          (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r) 1 ^ h)⁻¹ * t) := by
  have hn : ∀ v : D.E, nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (-v) =
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v)⁻¹ := by
    intro v
    exact nativeLieExponential_neg (E := D.E) (I := D.I) (G := D.G) v
  have hPow : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (((-h : ℤ) : ℝ) • roughVectorMvEval (E := D.E) (nativeBasepointPolynomial D p r) (fun _ => 1)) =
      (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r) 1 ^ h)⁻¹ := by
    rw [nativeLieExponential_int_smul,zpow_neg]
    congr 2
    simp only [nativeIntegerLogPolynomialSequence,Int.cast_one]
  simp only [nativeBasepointShiftRawPolynomial,roughNativeProductMvPolynomial_eval,
    rough_vector_constant_eval,nativeLieExponential_globalLogarithm,hn,hPow,
    roughVectorMvAffineSubstitution_eval]
  simp only [one_mul,add_comm (h : ℝ),mul_assoc]

theorem native_basepoint_shift_raw_weighted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
      (nativeBasepointShiftRawPolynomial D p r t h) 0 := by
  have hc : ∀ v : D.E, RoughVectorMvWeightedDegree
      (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) (roughVectorMvConstant (σ := Unit) v) 0 := by
    intro v
    apply rough_vector_constant_weighted
    rw [rough_native_stretched_lie_initial d hd 0 (Nat.zero_le d)]
    exact Submodule.mem_top
  unfold nativeBasepointShiftRawPolynomial
  apply rough_native_product_polynomial_weighted d hd (hc _)
  apply rough_native_product_polynomial_weighted d hd
    (rough_vector_weighted_affine _ (rough_native_stretched_lie_antitone d hd) _ _
      (native_basepoint_polynomial_weighted D d hd p hp r))
  exact rough_native_product_polynomial_weighted d hd (hc _) (hc _)

noncomputable def nativeBasepointShiftPolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (r t : D.G) (h : ℤ) : RoughVectorMvPolynomial Unit D.E :=
  roughVectorMvZeroTrim (nativeBasepointShiftRawPolynomial D p r t h)

theorem native_basepoint_shift_polynomial_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (r t : D.G) (h : ℤ) (x : Unit → ℝ) :
    roughVectorMvEval (E := D.E) (nativeBasepointShiftPolynomial D p r t h) x =
      roughVectorMvEval (E := D.E) (nativeBasepointShiftRawPolynomial D p r t h) x :=
  rough_vector_zero_trim_eval _ _

theorem native_basepoint_shift_polynomial_degree {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) : RoughVectorMvDegreeLE (nativeBasepointShiftPolynomial D p r t h) (s*d) :=
  rough_vector_zero_trim_degree _ (rough_native_stretched_lie_antitone d hd)
    (native_basepoint_shift_raw_weighted D d hd p hp r t h)
    (rough_native_stretched_lie_terminal d hd D.step_le)

end Hindman168
