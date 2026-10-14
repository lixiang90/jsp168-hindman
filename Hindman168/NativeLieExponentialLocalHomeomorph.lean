import Hindman168.NativeLieExponentialLocalLogAt
import Mathlib.Topology.IsLocalHomeomorph

/-! Actual local inverse laws imply that the original exponential is a
local homeomorphism and open map. Each original fiber is closed and
discrete; no global bijectivity or covering-map conclusion is asserted. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieExponential_image_mem_nhds_at {v : E} {U : Set E} (hU : U ∈ 𝓝 v) :
    (fun z : E => nativeLieExponential (I := I) (G := G) z) '' U ∈
      𝓝 (nativeLieExponential (I := I) (G := G) v) := by
  have ht := (nativeLieExponentialLocalLogAt_contMDiffAt (I := I) (G := G) v).continuousAt.tendsto
  rw [nativeLieExponentialLocalLogAt_self] at ht
  have hpre := ht.eventually hU
  filter_upwards [hpre, nativeLieExponentialLocalLogAt_right (I := I) (G := G) v] with g hg he
  exact ⟨nativeLieExponentialLocalLogAt (I := I) (G := G) v g, hg, he⟩

 theorem nativeLieExponential_isOpenMap :
    IsOpenMap (fun v : E => nativeLieExponential (I := I) (G := G) v) := by
  apply IsOpenMap.of_nhds_le
  intro v U hU
  have he := nativeLieExponential_image_mem_nhds_at (I := I) (G := G) hU
  exact mem_of_superset he (by rintro g ⟨z, hz, rfl⟩; exact hz)

 theorem nativeLieExponential_injOn_nhds (v : E) :
    ∃ U : Set E, U ∈ 𝓝 v ∧ InjOn (fun z : E => nativeLieExponential (I := I) (G := G) z) U := by
  refine ⟨{z : E | nativeLieExponentialLocalLogAt (I := I) (G := G) v
    (nativeLieExponential (I := I) (G := G) z) = z}, nativeLieExponentialLocalLogAt_left v, ?_⟩
  intro x hx y hy hxy
  exact hx.symm.trans ((congrArg (nativeLieExponentialLocalLogAt (I := I) (G := G) v) hxy).trans hy)

 theorem nativeLieExponential_isLocalHomeomorph :
    IsLocalHomeomorph (fun v : E => nativeLieExponential (I := I) (G := G) v) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro v
  obtain ⟨U, hU, hinj⟩ := nativeLieExponential_injOn_nhds (I := I) (G := G) v
  obtain ⟨V, hVU, hVo, hv⟩ := mem_nhds_iff.mp hU
  refine ⟨V, hVo.mem_nhds hv, ?_⟩
  have hc : Continuous (V.restrict (fun z : E => nativeLieExponential (I := I) (G := G) z)) :=
    (nativeLieExponential_contMDiff (I := I) (G := G)).continuous.comp continuous_subtype_val
  have hi : Injective (V.restrict (fun z : E => nativeLieExponential (I := I) (G := G) z)) :=
    Set.injOn_iff_injective.mp (hinj.mono hVU)
  have ho : IsOpenMap (V.restrict (fun z : E => nativeLieExponential (I := I) (G := G) z)) :=
    (nativeLieExponential_isOpenMap (I := I) (G := G)).comp hVo.isOpenMap_subtype_val
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hc hi ho

 theorem nativeLieExponential_map_nhds (v : E) :
    Filter.map (fun z : E => nativeLieExponential (I := I) (G := G) z) (𝓝 v) =
      𝓝 (nativeLieExponential (I := I) (G := G) v) :=
  (nativeLieExponential_isLocalHomeomorph (I := I) (G := G)).map_nhds_eq v

omit [Group.IsNilpotent G] in
 theorem nativeLieExponential_fiber_closed (g : G) :
    IsClosed {v : E | nativeLieExponential (I := I) (G := G) v = g} :=
  isClosed_singleton.preimage (nativeLieExponential_contMDiff (I := I) (G := G)).continuous

 theorem nativeLieExponential_fiber_discrete (g : G) :
    IsDiscrete {v : E | nativeLieExponential (I := I) (G := G) v = g} := by
  have hi : IsDiscrete ((fun v : E => nativeLieExponential (I := I) (G := G) v) ''
      {v : E | nativeLieExponential (I := I) (G := G) v = g}) := by
    apply (Set.subsingleton_singleton : ({g} : Set G).Subsingleton).isDiscrete.mono
    rintro x ⟨v, hv, rfl⟩
    exact hv
  exact (nativeLieExponential_isLocalHomeomorph (I := I) (G := G)).isLocalHomeomorphOn.isDiscrete_of_image hi

 theorem nativeLieExponential_range_open :
    IsOpen (Set.range (fun v : E => nativeLieExponential (I := I) (G := G) v)) := by
  simpa only [image_univ] using (nativeLieExponential_isOpenMap (I := I) (G := G)) univ isOpen_univ

end Hindman168
