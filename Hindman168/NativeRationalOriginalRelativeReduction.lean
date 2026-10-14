import Hindman168.NativeRationalWeightedDegreeReducedPolynomial
import Hindman168.NativeRationalWeightedNormalizations

/-! ACTUAL twice-normalized ORIGINAL ordinary-degree source feeds the true
relative-then-terminal degree reduction at SAME stretch d, not s*d. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeOriginalNormalizedRelativeReducedPolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) (r γ t : D.G) (h : ℤ) :
    RoughVectorMvPolynomial Unit (nativeRationalDegreeReducedData D (nativeOriginalRationalLieFiltration D d hd)).E :=
  nativeRationalWeightedDegreeReducedPolynomial D (nativeOriginalRationalLieFiltration D d hd)
    (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ)
    (native_basepoint_linear_step_polynomial_weighted D d hd p hp r γ)
    (native_two_normalizations_logarithmic_zero D p r γ) t h

theorem native_original_normalized_relative_reduced_polynomial_weighted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) (r γ t : D.G) (h : ℤ) :
    RoughVectorMvWeightedDegree (nativeDegreeReducedRationalLieFiltration D (nativeOriginalRationalLieFiltration D d hd)).layer
      (nativeOriginalNormalizedRelativeReducedPolynomial D d hd p hp r γ t h) 0 :=
  native_rational_weighted_degree_reduced_polynomial_weighted D (nativeOriginalRationalLieFiltration D d hd)
    _ (native_basepoint_linear_step_polynomial_weighted D d hd p hp r γ)
    (native_two_normalizations_logarithmic_zero D p r γ) t h

theorem native_original_normalized_relative_reduced_polynomial_degree {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) (r γ t : D.G) (h : ℤ) :
    RoughVectorMvDegreeLE (roughVectorMvZeroTrim (nativeOriginalNormalizedRelativeReducedPolynomial D d hd p hp r γ t h))
      (s*d-1) :=
  native_rational_weighted_degree_reduced_polynomial_degree_drop D (nativeOriginalRationalLieFiltration D d hd)
    _ (native_basepoint_linear_step_polynomial_weighted D d hd p hp r γ)
    (native_two_normalizations_logarithmic_zero D p r γ) t h

theorem native_original_normalized_relative_reduced_polynomial_sample {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) (r γ t : D.G) (h n : ℤ) :
    nativeMvPolynomialOrbit (nativeRationalDegreeReducedData D (nativeOriginalRationalLieFiltration D d hd))
      (nativeOriginalNormalizedRelativeReducedPolynomial D d hd p hp r γ t h) (fun _ => n) =
    nativeRationalTerminalFactorMap (nativeRationalRelativeData D (nativeOriginalRationalLieFiltration D d hd) 1)
      (nativeRelativeRationalLieFiltration D (nativeOriginalRationalLieFiltration D d hd))
      ((nativeRationalWeightedIntegerPair D (nativeOriginalRationalLieFiltration D d hd)
        (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ)
        (native_basepoint_linear_step_polynomial_weighted D d hd p hp r γ)
        (native_two_normalizations_logarithmic_zero D p r γ) t h n) :
        (nativeRationalRelativeData D (nativeOriginalRationalLieFiltration D d hd) 1).G ⧸
          (nativeRationalRelativeData D (nativeOriginalRationalLieFiltration D d hd) 1).Γ) :=
  native_rational_weighted_degree_reduced_polynomial_sample D (nativeOriginalRationalLieFiltration D d hd)
    _ (native_basepoint_linear_step_polynomial_weighted D d hd p hp r γ)
    (native_two_normalizations_logarithmic_zero D p r γ) t h n

end Hindman168
