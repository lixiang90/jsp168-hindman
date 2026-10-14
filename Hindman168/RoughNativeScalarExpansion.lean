import Hindman168.RoughJointScalarExpansion
import Hindman168.NativeNilmanifoldData
import Hindman168.NativeLieLogarithmCharacter

namespace Hindman168
open MvPolynomial
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def roughScalarSpatialProjection {κ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (χ : E →ₗ[ℝ] ℝ)
    (p : RoughVectorMvPolynomial (Option κ) E) (z : ℝ) : MvPolynomial κ ℝ :=
  map (Polynomial.evalRingHom z) (optionEquivRight ℝ κ (roughVectorMvProjection χ p))

theorem rough_native_scalar_expansion {κ : Type*} [Fintype κ] {step : ℕ}
    (D : NativeNilmanifoldData.{u} step) (χ : D.E →ₗ[ℝ] ℝ)
    (P : (Option κ → ℝ) → D.G) (p : RoughVectorMvPolynomial (Option κ) D.E)
    (q : ℕ) (hp : RoughVectorMvDegreeLE p q)
    (hlog : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (P x)) :
    ∃ (P0 : Polynomial ℝ) (θ : (κ →₀ ℕ) → Polynomial ℝ),
      P0.natDegree ≤ q ∧
      (∀ I ∈ roughSpatialDegreeSupport κ q, (θ I).natDegree+I.sum (fun _ e => e) ≤ q) ∧
      (∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) =
        eval x (roughSpatialJointPolynomial (roughSpatialDegreeSupport κ q) P0 θ)) ∧
      ∀ z : ℝ, roughScalarSpatialProjection χ p z =
        roughSpatialFixedPolynomial (roughSpatialDegreeSupport κ q) (P0.eval z)
          (fun I => (θ I).eval z) := by
  let f := roughVectorMvProjection χ p
  let θ := fun I => coeff I (optionEquivRight ℝ κ f)
  obtain ⟨he, h0, hθ⟩ := rough_fixed_scalar_joint_expansion f q (roughVectorMvProjection_degree χ hp)
  refine ⟨θ 0, θ, h0, hθ, ?_, ?_⟩
  · intro x
    change χ (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (P x)) = _
    rw [← hlog x, ← roughVectorMvProjection_eval]
    exact congrArg (eval x) he
  · intro z
    change map (Polynomial.evalRingHom z) (optionEquivRight ℝ κ f) = _
    rw [he, rough_joint_option_right]
    simp only [map_add, map_sum, map_C, map_monomial,
      roughSpatialFixedPolynomial]
    rfl

end Hindman168
