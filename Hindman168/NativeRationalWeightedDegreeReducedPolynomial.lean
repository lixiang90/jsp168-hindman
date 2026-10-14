import Hindman168.NativeRationalWeightedRelativeFiltered
import Hindman168.NativeRationalDegreeRecursion
import Hindman168.NativeRationalTerminalPolynomial

/-! The ACTUAL weighted relative polynomial projects to the ACTUAL degree
reduced native data, with exact original integer pair samples and degree drop. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalWeightedDegreeReducedPolynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (t : D.G) (h : ℤ) :
    RoughVectorMvPolynomial Unit (nativeRationalDegreeReducedData D F).E :=
  nativeRationalTerminalPolynomial (nativeRationalRelativeData D F 1) (nativeRelativeRationalLieFiltration D F)
    (nativeRationalWeightedRelativePolynomial D F p hp h0 t h)

theorem native_rational_weighted_degree_reduced_polynomial_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (t : D.G) (h : ℤ) :
    RoughVectorMvWeightedDegree (nativeDegreeReducedRationalLieFiltration D F).layer
      (nativeRationalWeightedDegreeReducedPolynomial D F p hp h0 t h) 0 :=
  native_rational_terminal_polynomial_weighted (nativeRationalRelativeData D F 1) (nativeRelativeRationalLieFiltration D F)
    (native_rational_weighted_relative_polynomial_weighted D F p hp h0 t h)

theorem native_rational_weighted_degree_reduced_polynomial_degree_drop {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (t : D.G) (h : ℤ) :
    RoughVectorMvDegreeLE (roughVectorMvZeroTrim (nativeRationalWeightedDegreeReducedPolynomial D F p hp h0 t h)) (ℓ-1) := by
  have he := native_rational_terminal_polynomial_zero_trim_degree
    (nativeRationalRelativeData D F 1) (nativeRelativeRationalLieFiltration D F)
    (native_rational_weighted_relative_polynomial_weighted D F p hp h0 t h)
  exact he

theorem native_rational_weighted_degree_reduced_polynomial_exponential {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (t : D.G) (h n : ℤ) :
    nativeLieExponential (E := (nativeRationalDegreeReducedData D F).E)
      (I := (nativeRationalDegreeReducedData D F).I) (G := (nativeRationalDegreeReducedData D F).G)
      (roughVectorMvEval (E := (nativeRationalDegreeReducedData D F).E)
        (nativeRationalWeightedDegreeReducedPolynomial D F p hp h0 t h) (fun _ => (n : ℝ))) =
    nativeRationalTerminalGroupProjection (nativeRationalRelativeData D F 1) (nativeRelativeRationalLieFiltration D F)
      (nativeRationalWeightedIntegerPair D F p hp h0 t h n) := by
  have he := native_rational_terminal_polynomial_exponential (nativeRationalRelativeData D F 1)
    (nativeRelativeRationalLieFiltration D F) (nativeRationalWeightedRelativePolynomial D F p hp h0 t h)
    (fun _ => (n : ℝ))
  rw [native_rational_weighted_relative_polynomial_exponential] at he
  exact he

theorem native_rational_weighted_degree_reduced_polynomial_sample {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (t : D.G) (h n : ℤ) :
    nativeMvPolynomialOrbit (nativeRationalDegreeReducedData D F)
      (nativeRationalWeightedDegreeReducedPolynomial D F p hp h0 t h) (fun _ => n) =
    nativeRationalTerminalFactorMap (nativeRationalRelativeData D F 1) (nativeRelativeRationalLieFiltration D F)
      ((nativeRationalWeightedIntegerPair D F p hp h0 t h n) :
        (nativeRationalRelativeData D F 1).G ⧸ (nativeRationalRelativeData D F 1).Γ) := by
  rw [← native_rational_weighted_relative_polynomial_orbit D F p hp h0 t h n]
  exact (native_rational_terminal_polynomial_integer_orbit (nativeRationalRelativeData D F 1)
    (nativeRelativeRationalLieFiltration D F) _ (fun _ => n)).symm

theorem native_rational_weighted_degree_reduced_polynomial_scalar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (t : D.G) (h : ℤ)
    (χ : (nativeRationalDegreeReducedData D F).E →ₗ[ℝ] ℝ) :
    roughVectorMvProjection χ (nativeRationalWeightedDegreeReducedPolynomial D F p hp h0 t h) =
    roughVectorMvProjection (χ.comp (nativeRationalTerminalModelProjection (nativeRationalRelativeData D F 1)
      (nativeRelativeRationalLieFiltration D F)).toLinearMap) (nativeRationalWeightedRelativePolynomial D F p hp h0 t h) :=
  native_rational_terminal_polynomial_scalar (nativeRationalRelativeData D F 1) (nativeRelativeRationalLieFiltration D F) _ χ

end Hindman168
