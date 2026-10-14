import Hindman168.NativeRationalTerminalPolynomial
import Hindman168.NativeTwoNormalizations

/-! ACTUAL twice-normalized ORIGINAL bounded-degree polynomial feeds the
true terminal quotient weighted-polynomial construction at SAME stretch d.
All input weights are discharged, not assumed at an enlarged ordinary degree. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeOriginalNormalizedTerminalPolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (r γ : D.G) :
    RoughVectorMvPolynomial Unit (nativeRationalTerminalQuotientData D (nativeOriginalRationalLieFiltration D d hd)).E :=
  nativeRationalTerminalPolynomial D (nativeOriginalRationalLieFiltration D d hd)
    (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ)

theorem native_original_normalized_terminal_polynomial_weighted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) (r γ : D.G) :
    RoughVectorMvWeightedDegree (nativeTerminalRationalLieFiltration D (nativeOriginalRationalLieFiltration D d hd)).layer
      (nativeOriginalNormalizedTerminalPolynomial D d hd p r γ) 0 :=
  native_rational_terminal_polynomial_weighted D (nativeOriginalRationalLieFiltration D d hd)
    (native_basepoint_linear_step_polynomial_weighted D d hd p hp r γ)

theorem native_original_normalized_terminal_polynomial_degree_drop {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) (r γ : D.G) :
    RoughVectorMvDegreeLE (roughVectorMvZeroTrim (nativeOriginalNormalizedTerminalPolynomial D d hd p r γ)) (s*d-1) := by
  have he := native_rational_terminal_polynomial_zero_trim_degree D (nativeOriginalRationalLieFiltration D d hd)
    (native_basepoint_linear_step_polynomial_weighted D d hd p hp r γ)
  simpa only [nativeOriginalNormalizedTerminalPolynomial,Nat.sub_zero] using he

theorem native_original_normalized_terminal_polynomial_original_orbit {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (r : D.G) (γ₀ γ₁ : D.Γ)
    (h0 : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p 0) = r*γ₀) (x : Unit → ℤ) :
    nativeRationalTerminalFactorMap D (nativeOriginalRationalLieFiltration D d hd)
      (r • nativeMvPolynomialOrbit D
        (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ₁) x) =
      nativeRationalTerminalFactorMap D (nativeOriginalRationalLieFiltration D d hd) (nativeMvPolynomialOrbit D p x) := by
  rw [native_two_normalizations_original_orbit D p r γ₀ γ₁ h0 x]

theorem native_original_normalized_terminal_polynomial_sample {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (r γ : D.G) (x : Unit → ℤ) :
    nativeMvPolynomialOrbit (nativeRationalTerminalQuotientData D (nativeOriginalRationalLieFiltration D d hd))
      (nativeOriginalNormalizedTerminalPolynomial D d hd p r γ) x =
        nativeRationalTerminalFactorMap D (nativeOriginalRationalLieFiltration D d hd)
          (nativeMvPolynomialOrbit D (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ) x) :=
  (native_rational_terminal_polynomial_integer_orbit D (nativeOriginalRationalLieFiltration D d hd) _ x).symm

end Hindman168
