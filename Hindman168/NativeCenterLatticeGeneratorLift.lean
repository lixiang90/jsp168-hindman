import Hindman168.NativeCenterQuotientRationalSpan

namespace Hindman168
open scoped Manifold ContDiff

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_center_lattice_generator_lifts (Γ : Subgroup G) :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
    let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
    let Q := G ⧸ Subgroup.center G
    ∀ v : ι → F, (∀ i, nativeLieExponential (I := 𝓘(ℝ, F)) (G := Q) (v i) ∈
      Γ.map (QuotientGroup.mk' (Subgroup.center G))) →
      ∃ u : ι → E, ∀ i,
        nativeLieExponential (I := I) (G := G) (u i) ∈ Γ ∧
        u i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ∧
        nativeCenterQuotientProjection (I := I) (G := G) (u i) = v i := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  dsimp only
  intro v hv
  have hl : ∀ i, ∃ γ : G, γ ∈ Γ ∧ QuotientGroup.mk γ =
      nativeLieExponential (I := 𝓘(ℝ, F)) (G := Q) (v i) := by
    intro i
    exact (Subgroup.mem_map).mp (hv i)
  choose γ hγ hq using hl
  refine ⟨fun i => nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (γ i), ?_⟩
  intro i
  refine ⟨?_, nativeSubgroup_logarithm_mem_span (E := E) (I := I) Γ (hγ i), ?_⟩
  · simpa only [nativeLieExponential_globalLogarithm] using hγ i
  · calc
      nativeCenterQuotientProjection (I := I) (G := G)
          (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (γ i)) =
        nativeLieGlobalLogarithm (E := F) (I := 𝓘(ℝ, F)) (G := Q) (QuotientGroup.mk (γ i)) :=
          (nativeCenterQuotient_nativeLogarithm_projection (I := I) (G := G) (γ i)).symm
      _ = nativeLieGlobalLogarithm (E := F) (I := 𝓘(ℝ, F)) (G := Q)
          (nativeLieExponential (I := 𝓘(ℝ, F)) (G := Q) (v i)) := congrArg _ (hq i)
      _ = v i := nativeLieGlobalLogarithm_exponential (I := 𝓘(ℝ, F)) (G := Q) (v i)

end Hindman168
