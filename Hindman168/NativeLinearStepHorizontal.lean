import Hindman168.NativeLinearStepPolynomial
import Hindman168.NativeLieLogarithmCharacter
import Mathlib.Algebra.MvPolynomial.Funext

/-! The COMPLETE original horizontal scalar polynomial under true lattice
linear-step correction. Only the linear coefficient changes, by an integer
for actual lattice-integral characters. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_linear_step_horizontal_projection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (γ : D.G)
    (f : D.E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ f.ker) :
    roughVectorMvProjection f (nativeLinearStepPolynomial D p γ) = roughVectorMvProjection f p -
      MvPolynomial.C (f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) γ))*MvPolynomial.X () := by
  apply MvPolynomial.funext
  intro x
  rw [map_sub,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,
    roughVectorMvProjection_eval,roughVectorMvProjection_eval,native_linear_step_polynomial_eval]
  have he := nativeLieLogarithmCharacter_mul f hf
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x))
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      ((-x ()) • nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) γ))
  rw [nativeLieLogarithmCharacter_exponential,nativeLieLogarithmCharacter_exponential,map_smul] at he
  simpa only [nativeLieLogarithmCharacter,ContinuousMap.coe_mk,smul_eq_mul,
    neg_mul,mul_comm,sub_eq_add_neg] using he

theorem native_linear_step_horizontal_coefficient {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (γ : D.G)
    (f : D.E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ f.ker) (J : Unit →₀ ℕ) :
    MvPolynomial.coeff J (roughVectorMvProjection f (nativeLinearStepPolynomial D p γ)) =
      MvPolynomial.coeff J (roughVectorMvProjection f p) -
        (if Finsupp.single () 1 = J then f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) γ) else 0) := by
  classical
  rw [native_linear_step_horizontal_projection D p γ f hf,MvPolynomial.coeff_sub,
    MvPolynomial.coeff_C_mul,MvPolynomial.coeff_X]
  split_ifs <;> simp only [mul_one,mul_zero]

theorem native_linear_step_horizontal_non_linear_coefficient {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (γ : D.G)
    (f : D.E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ f.ker)
    (J : Unit →₀ ℕ) (hJ : Finsupp.single () 1 ≠ J) :
    MvPolynomial.coeff J (roughVectorMvProjection f (nativeLinearStepPolynomial D p γ)) =
      MvPolynomial.coeff J (roughVectorMvProjection f p) := by
  rw [native_linear_step_horizontal_coefficient D p γ f hf J,if_neg hJ,sub_zero]

theorem native_linear_step_horizontal_coefficient_integer_shift {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (γ : D.Γ)
    (f : D.E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ f.ker)
    (hInt : ∀ g : D.Γ, ∃ z : ℤ, f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) = (z : ℝ))
    (J : Unit →₀ ℕ) :
    ∃ z : ℤ, MvPolynomial.coeff J (roughVectorMvProjection f (nativeLinearStepPolynomial D p γ)) =
      MvPolynomial.coeff J (roughVectorMvProjection f p)+(z : ℝ) := by
  obtain ⟨z,hz⟩ := hInt γ
  by_cases hJ : Finsupp.single () 1 = J
  · refine ⟨-z,?_⟩
    rw [native_linear_step_horizontal_coefficient D p γ f hf J,if_pos hJ,hz,Int.cast_neg,sub_eq_add_neg]
  · refine ⟨0,?_⟩
    rw [native_linear_step_horizontal_non_linear_coefficient D p γ f hf J hJ,Int.cast_zero,add_zero]

end Hindman168
