import Hindman168.LieInvariantCoordinateField

/-! Arbitrary-order regularity of the original native invariant field
for a smooth Lie group. All regularity comes from the tangent map of
the actual multiplication and the genuine identity chart. -/

namespace Hindman168
open Bundle Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

 theorem lieGroup_smooth_min_three : LieGroup I (minSmoothness ℝ 3) G := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using (inferInstance : LieGroup I 3 G)

attribute [local instance] lieGroup_smooth_min_three

 theorem lie_identity_tangent_inclusion_contMDiff_smooth :
    ContMDiff 𝓘(ℝ, E) I.tangent ∞
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

 theorem lie_invariant_field_joint_contMDiff_smooth :
    ContMDiff (𝓘(ℝ, E).prod I) I.tangent ∞
      (fun p : E × G => (⟨p.2, mulInvariantVectorField (I := I) p.1 p.2⟩ :
        TangentBundle I G)) := by
  let fg : E × G → TangentBundle I G := fun p => TotalSpace.mk' E p.2 0
  have hfg : ContMDiff (𝓘(ℝ, E).prod I) I.tangent ∞ fg :=
    (contMDiff_zeroSection _ _).comp contMDiff_snd
  let fv : E × G → TangentBundle I G := fun p => TotalSpace.mk' E 1 p.1
  have hfv : ContMDiff (𝓘(ℝ, E).prod I) I.tangent ∞ fv :=
    lie_identity_tangent_inclusion_contMDiff_smooth.comp contMDiff_fst
  let F₃ := tangentMap (I.prod I) I (fun p : G × G => p.1 * p.2)
  have h₃ : ContMDiff (I.prod I).tangent I.tangent ∞ F₃ := by
    exact (contMDiff_mul I ∞).contMDiff_tangentMap (by rw [ENat.coe_top_add_one])
  have h := (h₃.comp contMDiff_equivTangentBundleProd_symm).comp (hfg.prodMk hfv)
  convert! h with p
  · simp [F₃, fg, fv]
  · simp only [Function.comp_apply, tangentMap, F₃, fg, fv]
    rw [mfderiv_prod_eq_add_apply ((contMDiff_mul I ∞).mdifferentiableAt (by norm_num))]
    simp +instances [mulInvariantVectorField, equivTangentBundleProd]

variable [BoundarylessManifold I G]

 theorem lieInvariantCoordinateField_contDiffAt_smooth :
    ContDiffAt ℝ ∞ (lieInvariantCoordinateField (I := I) (G := G))
      (0, extChartAt I (1 : G) (1 : G)) := by
  have h := (lie_invariant_field_joint_contMDiff_smooth (I := I) (G := G)).contMDiffAt
    (x := (0, (1 : G)))
  rw [contMDiffAt_iff] at h
  have hc := h.2.contDiffAt (range_mem_nhds_isInteriorPoint
    (BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ, E).prod I) (x := (0, (1 : G)))))
  convert! hc.snd using 1

 theorem lieFrozenCoordinateField_contDiffAt_smooth :
    ContDiffAt ℝ ∞ (lieFrozenCoordinateField (I := I) (G := G))
      (0, extChartAt I (1 : G) (1 : G)) :=
  contDiffAt_const.prodMk (lieInvariantCoordinateField_contDiffAt_smooth (I := I) (G := G))

end Hindman168
