import Hindman168.LieInvariantIntegralCurves

/-! Joint regularity of the genuine native invariant vector field in
its tangent parameter and group point. It is obtained from the tangent
map of the actual group multiplication, not from supplied ODE data. -/

namespace Hindman168
open Bundle Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G]

 theorem lie_identity_tangent_inclusion_contMDiff :
    ContMDiff 𝓘(ℝ, E) I.tangent (minSmoothness ℝ 2)
      (fun v : E => (⟨(1 : G), v⟩ : TangentBundle I G)) := by
  intro v
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_const, ?_⟩
  have heq : (fun w : E =>
      (trivializationAt E (TangentSpace I) (1 : G)
        (⟨(1 : G), w⟩ : TangentBundle I G)).2) = id := by
    funext w
    rw [TangentBundle.trivializationAt_apply]
    exact tangentCoordChange_self (mem_extChartAt_source (I := I) (1 : G))
  rw [heq]
  exact contMDiffAt_id

 theorem lie_invariant_field_joint_contMDiff :
    ContMDiff (𝓘(ℝ, E).prod I) I.tangent (minSmoothness ℝ 2)
      (fun p : E × G => (⟨p.2, mulInvariantVectorField (I := I) p.1 p.2⟩ :
        TangentBundle I G)) := by
  have hn : minSmoothness ℝ 3 ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℕ∞ω) < 3) le_minSmoothness).ne'
  have hs : minSmoothness ℝ 2 + 1 = minSmoothness ℝ 3 := by
    rw [← minSmoothness_add]
    norm_num
  let fg : E × G → TangentBundle I G := fun p => TotalSpace.mk' E p.2 0
  have hfg : ContMDiff (𝓘(ℝ, E).prod I) I.tangent (minSmoothness ℝ 2) fg :=
    (contMDiff_zeroSection _ _).comp contMDiff_snd
  let fv : E × G → TangentBundle I G := fun p => TotalSpace.mk' E 1 p.1
  have hfv : ContMDiff (𝓘(ℝ, E).prod I) I.tangent (minSmoothness ℝ 2) fv :=
    lie_identity_tangent_inclusion_contMDiff.comp contMDiff_fst
  let F₁ := fun p : E × G => (fg p, fv p)
  let F₂ := (equivTangentBundleProd I G I G).symm
  let F₃ := tangentMap (I.prod I) I (fun p : G × G => p.1 * p.2)
  have h₃ : ContMDiff (I.prod I).tangent I.tangent (minSmoothness ℝ 2) F₃ := by
    apply ContMDiff.contMDiff_tangentMap _ (m := minSmoothness ℝ 2) le_rfl
    rw [hs]
    exact contMDiff_mul I (minSmoothness ℝ 3)
  have h := (h₃.comp contMDiff_equivTangentBundleProd_symm).comp (hfg.prodMk hfv)
  convert! h with p
  · simp [F₃, fg, fv]
  · simp only [Function.comp_apply, tangentMap, F₃, fg, fv]
    rw [mfderiv_prod_eq_add_apply
      ((contMDiff_mul I (minSmoothness ℝ 3)).mdifferentiableAt hn)]
    simp +instances [mulInvariantVectorField, equivTangentBundleProd]

 theorem lie_invariant_field_joint_contMDiff_one :
    ContMDiff (𝓘(ℝ, E).prod I) I.tangent 1
      (fun p : E × G => (⟨p.2, mulInvariantVectorField (I := I) p.1 p.2⟩ :
        TangentBundle I G)) :=
  lie_invariant_field_joint_contMDiff.of_le
    (le_trans (by norm_num : (1 : ℕ∞ω) ≤ 2) le_minSmoothness)

end Hindman168
