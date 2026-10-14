import Hindman168.NativeRationalScalarDifferenceFormula

/-! TRUE degree and zero/first-value normalization of the CONSTRUCTED
original F_2 nonlinear scalar polynomial. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_nonlinear_ambient_degree {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0) :
    RoughVectorMvDegreeLE (nativeLinearStepPolynomial D p (nativeIntegerLogPolynomialSequence D p 1)) ℓ := by
  have hw := native_rational_product_polynomial_weighted D L hp
    (show RoughVectorMvWeightedDegree L.layer
      (nativeLinearStepCorrection D (nativeIntegerLogPolynomialSequence D p 1)) 0 from by
        rintro a ha
        have he := List.mem_singleton.mp ha
        subst a
        simp only [MvPolynomial.totalDegree_X,Nat.add_zero]
        rw [L.one]
        exact Submodule.mem_top)
  have hd := rough_vector_zero_trim_degree L.layer L.antitone hw L.terminal
  simpa only [nativeLinearStepPolynomial,nativeLinearStepRawPolynomial,Nat.sub_zero] using hd

theorem native_rational_nonlinear_scalar_degree {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) :
    (nativeRationalNonlinearScalar D L p hp h0 χ).totalDegree ≤ ℓ :=
  roughVectorMvProjection_degree _
    (rough_vector_submodule_polynomial_degree _ _ _ (native_rational_nonlinear_ambient_degree D L p hp))

theorem native_rational_nonlinear_group_zero {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) :
    nativeRationalNonlinearGroup D L p hp h0 0 = 1 := by
  apply Subtype.ext
  change nativeIntegerLogPolynomialSequence D p 0*(nativeIntegerLogPolynomialSequence D p 1^0)⁻¹ = 1
  simp only [zpow_zero,inv_one,mul_one,nativeIntegerLogPolynomialSequence,Int.cast_zero,h0]
  exact nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G)

theorem native_rational_nonlinear_group_one {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) :
    nativeRationalNonlinearGroup D L p hp h0 1 = 1 := by
  apply Subtype.ext
  change nativeIntegerLogPolynomialSequence D p 1*(nativeIntegerLogPolynomialSequence D p 1^1)⁻¹ = 1
  simp only [zpow_one,mul_inv_cancel]

theorem native_rational_nonlinear_scalar_zero_one {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) :
    MvPolynomial.eval (fun _ => 0) (nativeRationalNonlinearScalar D L p hp h0 χ) = 0 ∧
    MvPolynomial.eval (fun _ => 1) (nativeRationalNonlinearScalar D L p hp h0 χ) = 0 := by
  have hzero : nativeRationalRelativeDifferenceLogCharacter D L χ 1 = 0 := by
    change χ (nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D L 1).E)
      (I := (nativeRationalRelativeData D L 1).I) (G := (nativeRationalRelativeData D L 1).G)
        (nativeRationalRelativeFirstDifferenceGroup D L 1)) = 0
    rw [map_one,nativeLieGlobalLogarithm_one,map_zero]
  constructor
  · have he := native_rational_nonlinear_scalar_integer D L p hp h0 χ 0
    simpa only [Int.cast_zero,native_rational_nonlinear_group_zero,hzero] using he
  · have he := native_rational_nonlinear_scalar_integer D L p hp h0 χ 1
    simpa only [Int.cast_one,native_rational_nonlinear_group_one,hzero] using he

end Hindman168
