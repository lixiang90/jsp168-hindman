import Hindman168.NativeBasepointTrimmedPolynomial
import Hindman168.NativeBasepointCharacter
import Mathlib.Algebra.MvPolynomial.Funext

/-! COMPLETE actual scalar polynomial compatibility under original
basepoint normalization. All nonconstant original coefficients are retained. -/

namespace Hindman168
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_basepoint_horizontal_projection {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (r : D.G)
    (f : D.E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ f.ker) :
    roughVectorMvProjection f (nativeBasepointPolynomial D p r) =
      roughVectorMvProjection f p - MvPolynomial.C (f (roughVectorMvEval (E := D.E) p 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [roughVectorMvProjection_eval,map_sub,MvPolynomial.eval_C,roughVectorMvProjection_eval,
    native_basepoint_polynomial_eval]
  have h := native_basepoint_character_value D f hf
    (fun y : σ → ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p y)) r x
  have he : ∀ v : D.E, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v) = v :=
    nativeLieGlobalLogarithm_exponential (E := D.E) (I := D.I) (G := D.G)
  simpa only [he] using h

theorem native_basepoint_horizontal_projection_coeff {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (r : D.G)
    (f : D.E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ f.ker) (J : σ →₀ ℕ) :
    MvPolynomial.coeff J (roughVectorMvProjection f (nativeBasepointPolynomial D p r)) =
      MvPolynomial.coeff J (roughVectorMvProjection f p) -
        (if 0 = J then f (roughVectorMvEval (E := D.E) p 0) else 0) := by
  classical
  rw [native_basepoint_horizontal_projection D p r f hf,MvPolynomial.coeff_sub,MvPolynomial.coeff_C]

theorem native_basepoint_horizontal_nonconstant_coeff {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (r : D.G)
    (f : D.E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ f.ker)
    (J : σ →₀ ℕ) (hJ : J ≠ 0) :
    MvPolynomial.coeff J (roughVectorMvProjection f (nativeBasepointPolynomial D p r)) =
      MvPolynomial.coeff J (roughVectorMvProjection f p) := by
  rw [native_basepoint_horizontal_projection D p r f hf,MvPolynomial.coeff_sub,
    MvPolynomial.coeff_C_of_ne_zero hJ,sub_zero]

end Hindman168
