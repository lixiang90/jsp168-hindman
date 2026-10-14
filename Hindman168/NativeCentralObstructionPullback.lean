import Hindman168.NativeCentralPolynomialProjection
import Hindman168.RoughNativeScalarExpansion

/-! Actual child scalar obstructions pull back to the ORIGINAL finite
horizontal grid, with original coefficients and a fixed parent budget. -/

namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_central_spatial_projection {s : ℕ} {κ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial (Option κ) D.E)
    (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ) (z : ℝ) :
    roughScalarSpatialProjection χ.toLinearMap (nativeCentralPolynomialProjection D p) z =
      roughScalarSpatialProjection (nativeCentralCharacterPullback D χ).toLinearMap p z := by
  unfold roughScalarSpatialProjection
  rw [native_central_polynomial_projection_scalar]

theorem native_central_monomial_obstruction_pullback {s : ℕ} {κ : Type*} [Fintype κ]
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial κ D.E)
    (A N : ℝ) (hA : 0 ≤ A) (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ)
    (hχ : ‖χ‖ ≤ A)
    (hHor : RoughNativeHorizontalFunctional (E := (nativeCentralQuotientData D).E)
      (I := (nativeCentralQuotientData D).I) (nativeCentralQuotientData D).Γ χ.toLinearMap)
    (hCoeff : ∀ J : κ → ℕ, 0 < ∑ i, J i →
      N^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
        (roughVectorMvProjection χ.toLinearMap (nativeCentralPolynomialProjection D p)) : ℝ) : UnitAddCircle)‖ ≤ A) :
    ∃ ψ : D.E →L[ℝ] ℝ,
      RoughNativeHorizontalFunctional (E := D.E) (I := D.I) D.Γ ψ.toLinearMap ∧
      ψ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (E := D.E) (I := D.I) D.Γ
        (nativeCentralCharacterBudget D A) ∧
      ‖ψ‖ ≤ nativeCentralCharacterBudget D A ∧
      ∀ J : κ → ℕ, 0 < ∑ i, J i →
        N^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
          (roughVectorMvProjection ψ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ nativeCentralCharacterBudget D A := by
  refine ⟨nativeCentralCharacterPullback D χ,
    native_central_character_pullback_horizontal D χ hHor,
    native_central_character_pullback_grid D A hA χ hχ hHor,
    native_central_character_pullback_bound D A hA χ hχ, ?_⟩
  intro J hJ
  rw [← native_central_polynomial_projection_scalar]
  exact (hCoeff J hJ).trans (native_central_character_budget_ge D A hA)

end Hindman168
