import Hindman168.RoughNativeActionFreezing
import Hindman168.RoughJointSlowOscillation

namespace Hindman168
open MvPolynomial
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_model_subbox_freezing {κ : Type*} [Fintype κ] {step : ℕ}
    (D : NativeNilmanifoldData.{u} step) (V : D.E)
    (s : Finset (κ →₀ ℕ)) (d : ℕ) (hd : ∀ J ∈ s, (∑ j, J j) ≤ d)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 1 ≤ C) (L : NNReal) {ε : ℝ} (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ r : ℝ, 0 < r ∧ ∀ (w H q z : ℕ) (Z : ℝ)
      (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)
      (M0 : Polynomial ℚ) (M : (κ →₀ ℕ) → Polynomial ℚ),
      (∀ J ∈ s, RoughCoefficientModel w H q (∑ j, J j) Z A (theta J) (M J)) →
      z < H → 0 < Z →
      (0 ≤ P0.eval (z : ℝ) - (((M0.eval (z : ℚ) : ℚ) : ℝ)) ∧
        P0.eval (z : ℝ) - (((M0.eval (z : ℚ) : ℚ) : ℝ)) < 1) →
      ∀ F : (D.G ⧸ D.Γ) → ℝ, LipschitzWith L F →
      ∀ (x y : κ → ℝ) (v : D.G ⧸ D.Γ),
      (∀ j, |x j| ≤ C * Z) → (∀ j, |y j| ≤ C * Z) →
      (∀ j, |x j - y j| ≤ r * Z) →
      let a := roughSpatialJointPolynomial s P0 theta -
        map (Rat.castHom ℝ) (roughSpatialJointPolynomial s M0 M)
      |F (nativeLieExponential (I := D.I) (G := D.G)
          (eval (Option.elim · (z : ℝ) x) a • V) • v) -
        F (nativeLieExponential (I := D.I) (G := D.G)
          (eval (Option.elim · (z : ℝ) y) a • V) • v)| < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  let B : ℝ := 1 + (s.card : ℝ) * A * C ^ d
  let K : ℝ := (s.card : ℝ) * d * A * C ^ d
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  obtain ⟨r, hr, hfreeze⟩ := rough_native_scalar_test_freezing D V B K hK L hε
  refine ⟨r, hr, ?_⟩
  intro w H q z Z P0 theta M0 M hmodels hz hZ h0 F hF x y v hx hy hxy
  apply hfreeze F hF _ _ v
  · exact rough_joint_horizontal_error_box s d hd P0 theta M0 M hmodels hz hA hC hZ h0 x hx
  · exact rough_joint_horizontal_error_box s d hd P0 theta M0 M hmodels hz hA hC hZ h0 y hy
  · exact rough_joint_slow_subbox_oscillation s d hd P0 theta M0 M hmodels hz hA hC hZ hr.le x y hx hy hxy

end Hindman168
