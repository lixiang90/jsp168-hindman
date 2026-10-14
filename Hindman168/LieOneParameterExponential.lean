import Hindman168.LieInvariantIntegralCurves
import Mathlib.Algebra.Group.TypeTags.Hom

/-! A genuine general real Lie-group exponential, constructed from the
proved global integral curve of the native invariant field. Uniqueness
proves the one-parameter group law and scalar reparametrization. Smoothness
in the Lie-algebra parameter and nilpotent global bijectivity are separate
remaining tasks; neither is assumed here. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G] [BoundarylessManifold I G] [T2Space G]

 omit [CompleteSpace E] in
 theorem lie_invariant_integralCurve_mul_add
    (v : GroupLieAlgebra I G) {γ : ℝ → G}
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) (hγ0 : γ 0 = 1)
    (r s : ℝ) : γ (r + s) = γ r * γ s := by
  have heq := lie_invariant_integralCurve_unique v (hγ.comp_add r)
    (lie_invariant_integralCurve_left_translate v hγ (γ r)) (t₀ := 0) (by
      simp only [Function.comp_apply, zero_add, hγ0, mul_one])
  have h := congrFun heq s
  simpa only [Function.comp_apply, add_comm s r] using h

 noncomputable def lieOneParameterCurve (v : GroupLieAlgebra I G) : ℝ → G :=
  Classical.choose (lie_invariant_integralCurve_exists_global v (1 : G))

 theorem lieOneParameterCurve_zero (v : GroupLieAlgebra I G) :
    lieOneParameterCurve v 0 = 1 :=
  (Classical.choose_spec (lie_invariant_integralCurve_exists_global v (1 : G))).1

 theorem lieOneParameterCurve_integral (v : GroupLieAlgebra I G) :
    IsMIntegralCurve (lieOneParameterCurve v) (mulInvariantVectorField v) :=
  (Classical.choose_spec (lie_invariant_integralCurve_exists_global v (1 : G))).2

 theorem lieOneParameterCurve_add (v : GroupLieAlgebra I G) (r s : ℝ) :
    lieOneParameterCurve v (r + s) = lieOneParameterCurve v r * lieOneParameterCurve v s :=
  lie_invariant_integralCurve_mul_add v (lieOneParameterCurve_integral v)
    (lieOneParameterCurve_zero v) r s

 noncomputable def lieOneParameterHom (v : GroupLieAlgebra I G) : ℝ →+ Additive G where
  toFun t := Additive.ofMul (lieOneParameterCurve v t)
  map_zero' := lieOneParameterCurve_zero v
  map_add' r s := lieOneParameterCurve_add v r s

 theorem lieOneParameterCurve_continuous (v : GroupLieAlgebra I G) :
    Continuous (lieOneParameterCurve v) := (lieOneParameterCurve_integral v).continuous

 theorem lieOneParameterCurve_unique (v : GroupLieAlgebra I G) {γ : ℝ → G}
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) (hγ0 : γ 0 = 1) :
    γ = lieOneParameterCurve v :=
  lie_invariant_integralCurve_unique v hγ (lieOneParameterCurve_integral v)
    (t₀ := 0) (hγ0.trans (lieOneParameterCurve_zero v).symm)

 theorem lieOneParameterCurve_smul (v : GroupLieAlgebra I G) (a : ℝ) :
    lieOneParameterCurve (a • v) = lieOneParameterCurve v ∘ (fun t : ℝ => t * a) := by
  have hc := (lieOneParameterCurve_integral v).comp_mul a
  rw [← mulInvariantVectorField_smul a v] at hc
  apply (lieOneParameterCurve_unique (a • v) hc ?_).symm
  simp only [Function.comp_apply, zero_mul, lieOneParameterCurve_zero]

 noncomputable def nativeLieExponential (v : GroupLieAlgebra I G) : G :=
  lieOneParameterCurve v 1

 theorem nativeLieExponential_smul (v : GroupLieAlgebra I G) (t : ℝ) :
    nativeLieExponential (t • v) = lieOneParameterCurve v t := by
  unfold nativeLieExponential
  rw [lieOneParameterCurve_smul]
  simp only [Function.comp_apply, one_mul]

 theorem nativeLieExponential_zero :
    nativeLieExponential (0 : GroupLieAlgebra I G) = 1 := by
  have hc : IsMIntegralCurve (fun _ : ℝ => (1 : G))
      (mulInvariantVectorField (0 : GroupLieAlgebra I G)) :=
    isMIntegralCurve_const (by
      simp only [mulInvariantVectorField, map_zero]
      rfl)
  have h := lieOneParameterCurve_unique (0 : GroupLieAlgebra I G) hc rfl
  exact (congrFun h 1).symm

 theorem nativeLieExponential_add_smul (v : GroupLieAlgebra I G) (r s : ℝ) :
    nativeLieExponential ((r + s) • v) =
      nativeLieExponential (r • v) * nativeLieExponential (s • v) := by
  simp only [nativeLieExponential_smul, lieOneParameterCurve_add]

 theorem nativeLieExponential_neg (v : GroupLieAlgebra I G) :
    nativeLieExponential (-v) = (nativeLieExponential v)⁻¹ := by
  have h := lieOneParameterCurve_add v (1 : ℝ) (-1)
  simp only [add_neg_cancel, lieOneParameterCurve_zero] at h
  have hi : lieOneParameterCurve v (-1) = (lieOneParameterCurve v 1)⁻¹ :=
    eq_inv_of_mul_eq_one_right h.symm
  rw [← neg_one_smul ℝ v, nativeLieExponential_smul, hi]
  rfl

end Hindman168
