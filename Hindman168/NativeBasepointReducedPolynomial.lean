import Hindman168.NativeBasepointRelativePolynomial
import Hindman168.NativeRelativeReductionPolynomial

/-! The ACTUAL original normalized shifted polynomial projects to the
SAME native terminal quotient. Complete scalar polynomials, coefficients
and original integer samples are retained without a relative-membership premise. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeBasepointReducedPolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) : RoughVectorMvPolynomial Unit (nativeRelativeReducedData D d hd).E :=
  nativeRelativeReductionPolynomial D d hd (nativeBasepointRelativePolynomial D d hd p hp r t h)

theorem native_basepoint_reduced_polynomial_degree {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) : RoughVectorMvDegreeLE (nativeBasepointReducedPolynomial D d hd p hp r t h) (s*d) :=
  native_relative_reduction_polynomial_degree D d hd _ _ (native_basepoint_relative_polynomial_degree D d hd p hp r t h)

theorem native_basepoint_reduced_polynomial_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) (x : Unit → ℝ) :
    roughVectorMvEval (E := (nativeRelativeReducedData D d hd).E)
      (nativeBasepointReducedPolynomial D d hd p hp r t h) x =
    nativeRelativeReductionModelProjection D d hd
      (roughVectorMvEval (E := (nativeRelativeSquareData D d hd 1).E)
        (nativeBasepointRelativePolynomial D d hd p hp r t h) x) :=
  native_relative_reduction_polynomial_eval D d hd _ x

theorem native_basepoint_reduced_polynomial_orbit {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h n : ℤ) :
    nativeMvPolynomialOrbit (nativeRelativeReducedData D d hd)
      (nativeBasepointReducedPolynomial D d hd p hp r t h) (fun _ => n) =
      nativeRelativeReductionFactorMap D d hd
        (nativeBasepointRelativeIntegerPair D d hd p hp r t h n :
          (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ) := by
  change nativeMvPolynomialOrbit (nativeRelativeReducedData D d hd)
    (nativeRelativeReductionPolynomial D d hd (nativeBasepointRelativePolynomial D d hd p hp r t h)) (fun _ => n) = _
  rw [← native_relative_reduction_polynomial_orbit,native_basepoint_relative_polynomial_orbit]

theorem native_basepoint_reduced_polynomial_scalar {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) (χ : (nativeRelativeReducedData D d hd).E →L[ℝ] ℝ) :
    roughVectorMvProjection χ.toLinearMap (nativeBasepointReducedPolynomial D d hd p hp r t h) =
      roughVectorMvProjection (χ.comp (nativeRelativeReductionModelProjection D d hd)).toLinearMap
        (nativeBasepointRelativePolynomial D d hd p hp r t h) :=
  native_relative_reduction_polynomial_scalar D d hd _ χ

theorem native_basepoint_reduced_polynomial_coeff {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) (χ : (nativeRelativeReducedData D d hd).E →L[ℝ] ℝ) (J : Unit →₀ ℕ) :
    MvPolynomial.coeff J (roughVectorMvProjection χ.toLinearMap (nativeBasepointReducedPolynomial D d hd p hp r t h)) =
      MvPolynomial.coeff J (roughVectorMvProjection
        (χ.comp (nativeRelativeReductionModelProjection D d hd)).toLinearMap
          (nativeBasepointRelativePolynomial D d hd p hp r t h)) := by
  rw [native_basepoint_reduced_polynomial_scalar]

end Hindman168
