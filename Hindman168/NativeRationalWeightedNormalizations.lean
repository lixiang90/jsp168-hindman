import Hindman168.NativeRationalWeightedOperations
import Hindman168.NativeTwoNormalizations

/-! Both ACTUAL native normalizations retain any true rational Lie weights.
This supplies the input normalization at later true IMAGE filtration stages. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_weighted_basepoint_polynomial {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {p : RoughVectorMvPolynomial σ D.E} (hp : RoughVectorMvWeightedDegree F.layer p 0) (r : D.G) :
    RoughVectorMvWeightedDegree F.layer (nativeBasepointPolynomial D p r) 0 := by
  apply rough_vector_zero_trim_weighted
  unfold nativeBasepointRawPolynomial
  apply native_rational_product_polynomial_weighted D F (native_rational_constant_zero_weighted D F _)
  apply native_rational_product_polynomial_weighted D F hp
  exact native_rational_product_polynomial_weighted D F
    (native_rational_constant_zero_weighted D F _) (native_rational_constant_zero_weighted D F _)

theorem native_rational_weighted_linear_step_polynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {p : RoughVectorMvPolynomial Unit D.E} (hp : RoughVectorMvWeightedDegree F.layer p 0) (γ : D.G) :
    RoughVectorMvWeightedDegree F.layer (nativeLinearStepPolynomial D p γ) 0 := by
  apply rough_vector_zero_trim_weighted
  apply native_rational_product_polynomial_weighted D F hp
  rintro a ha
  have he : a = (MvPolynomial.X (),-nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) γ) :=
    List.mem_singleton.mp ha
  subst a
  simp only [MvPolynomial.totalDegree_X,Nat.add_zero]
  rw [F.one]
  exact Submodule.mem_top

theorem native_two_normalizations_logarithmic_zero {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (r γ : D.G) :
    roughVectorMvEval (E := D.E) (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ)
      (fun _ => 0) = 0 := by
  have he := congrArg (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G))
    (native_two_normalizations_zero D p r γ)
  simpa only [nativeLieGlobalLogarithm_exponential,nativeLieGlobalLogarithm_one] using he

theorem native_rational_weighted_two_normalizations {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {p : RoughVectorMvPolynomial Unit D.E} (hp : RoughVectorMvWeightedDegree F.layer p 0) (r γ : D.G) :
    RoughVectorMvWeightedDegree F.layer (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ) 0 :=
  native_rational_weighted_linear_step_polynomial D F (native_rational_weighted_basepoint_polynomial D F hp r) γ

theorem native_rational_weighted_two_normalizations_degree {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {p : RoughVectorMvPolynomial Unit D.E} (hp : RoughVectorMvWeightedDegree F.layer p 0) (r γ : D.G) :
    RoughVectorMvDegreeLE (nativeLinearStepPolynomial D (nativeBasepointPolynomial D p r) γ) ℓ := by
  have he := rough_vector_zero_trim_degree F.layer F.antitone
    (native_rational_product_polynomial_weighted D F
      (native_rational_weighted_basepoint_polynomial D F hp r)
      (by
        rintro a ha
        have hh : a = (MvPolynomial.X (),-nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) γ) :=
          List.mem_singleton.mp ha
        subst a
        simp only [MvPolynomial.totalDegree_X,Nat.add_zero]
        rw [F.one]
        exact Submodule.mem_top)) F.terminal
  simpa only [nativeLinearStepPolynomial,nativeLinearStepRawPolynomial,nativeLinearStepCorrection,Nat.sub_zero] using he

end Hindman168
