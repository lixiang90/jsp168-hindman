import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-! Global integral curves of actual native left-invariant fields on
arbitrary real Lie groups. Local existence at the identity is transported
by genuine left multiplication, giving a common time interval at all
points and therefore global existence. No global curve is assumed. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G]

 theorem lie_invariant_field_left_derivative
    (v : GroupLieAlgebra I G) (g h : G) :
    mfderiv I I (fun x : G => g * x) h (mulInvariantVectorField v h) =
      mulInvariantVectorField v (g * h) := by
  have hn : minSmoothness ℝ 3 ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℕ∞ω) < 3) le_minSmoothness).ne'
  have hdg : MDifferentiableAt I I (fun x : G => g * x) h :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt hn
  have hdh : MDifferentiableAt I I (fun x : G => h * x) (1 : G) :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt hn
  have hc := mfderiv_comp_apply_of_eq (I := I) (I' := I) (I'' := I)
    (1 : G) hdg hdh (mul_one h) v
  have heq : (fun x : G => g * x) ∘ (fun x : G => h * x) =
      (fun x : G => (g * h) * x) := by
    funext x
    exact (mul_assoc g h x).symm
  rw [heq] at hc
  exact hc.symm


 theorem lie_invariant_field_contMDiff_one (v : GroupLieAlgebra I G) :
    ContMDiff I I.tangent 1
      (fun g : G => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle I G)) := by
  exact (contMDiff_mulInvariantVectorField v).of_le
    (le_trans (by norm_num : (1 : ℕ∞ω) ≤ 2) le_minSmoothness)

 theorem lie_invariant_integralCurveOn_left_translate
    (v : GroupLieAlgebra I G) {γ : ℝ → G} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ (mulInvariantVectorField v) s) (g : G) :
    IsMIntegralCurveOn (fun t => g * γ t) (mulInvariantVectorField v) s := by
  intro t ht
  have hn : minSmoothness ℝ 3 ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℕ∞ω) < 3) le_minSmoothness).ne'
  have hd : MDifferentiableAt I I (fun x : G => g * x) (γ t) :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt hn
  apply (hd.hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht)).congr_mfderiv
  change (mfderiv I I (fun x : G => g * x) (γ t) : E →L[ℝ] E).comp
    ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (γ t) : E)) =
    (1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (g * γ t) : E)
  apply ContinuousLinearMap.ext
  intro a
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, map_smul]
  erw [lie_invariant_field_left_derivative]

 theorem lie_invariant_integralCurve_left_translate
    (v : GroupLieAlgebra I G) {γ : ℝ → G}
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) (g : G) :
    IsMIntegralCurve (fun t => g * γ t) (mulInvariantVectorField v) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ ⊢
  exact lie_invariant_integralCurveOn_left_translate v hγ g

variable [CompleteSpace E] [BoundarylessManifold I G]

 theorem lie_invariant_integralCurve_uniform_local (v : GroupLieAlgebra I G) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : G, ∃ γ : ℝ → G,
      γ 0 = g ∧ IsMIntegralCurveOn γ (mulInvariantVectorField v) (Ioo (-ε) ε) := by
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (I := I) (x₀ := (1 : G))
      (0 : ℝ) (lie_invariant_field_contMDiff_one v).contMDiffAt
  obtain ⟨ε, hε, hγε⟩ := isMIntegralCurveAt_iff'.mp hγ
  refine ⟨ε, hε, fun g => ⟨fun t => g * γ t, ?_, ?_⟩⟩
  · change g * γ 0 = g
    rw [hγ0, mul_one]
  · simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using
      lie_invariant_integralCurveOn_left_translate v hγε g

variable [T2Space G]

 theorem lie_invariant_integralCurve_exists_global (v : GroupLieAlgebra I G) (g : G) :
    ∃ γ : ℝ → G, γ 0 = g ∧ IsMIntegralCurve γ (mulInvariantVectorField v) := by
  obtain ⟨ε, hε, h⟩ := lie_invariant_integralCurve_uniform_local v
  exact exists_isMIntegralCurve_of_isMIntegralCurveOn
    (lie_invariant_field_contMDiff_one v) hε h g

 omit [CompleteSpace E] in
 theorem lie_invariant_integralCurve_unique (v : GroupLieAlgebra I G)
    {γ η : ℝ → G} (hγ : IsMIntegralCurve γ (mulInvariantVectorField v))
    (hη : IsMIntegralCurve η (mulInvariantVectorField v)) {t₀ : ℝ}
    (h : γ t₀ = η t₀) : γ = η :=
  isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
    (lie_invariant_field_contMDiff_one v) hγ hη h

end Hindman168
