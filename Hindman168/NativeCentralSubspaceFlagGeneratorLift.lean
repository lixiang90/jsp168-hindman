import Hindman168.NativeCentralSubspaceLayerLatticeLift
import Mathlib.Data.Finset.Max

/-! A single original lattice lift preserves every specified earlier
lower-central membership. Choose the deepest actual quotient layer first. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

theorem native_central_subspace_lattice_flag_generator_lifts (Γ : Subgroup G)
    (V : Submodule ℝ E) [IsClosed (V : Set E)]
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) (j : ℕ)
    (hprior : ∀ k ≤ j, V ≤ nativeLieLowerCentralModel (I := I) (G := G) k) :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
    letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
    letI := nativeCentralSubspaceQuotient_simplyConnected (I := I) V hV
    let F := E ⧸ V
    let Q := G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV
    ∀ v : ι → F,
      (∀ i, nativeLieExponential (I := 𝓘(ℝ, F)) (G := Q) (v i) ∈
        Γ.map (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV))) →
      ∃ u : ι → E, ∀ i,
        nativeLieExponential (I := I) (G := G) (u i) ∈ Γ ∧
        u i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ∧
        finiteRealQuotientProjection V (u i) = v i ∧
        ∀ k ≤ j, u i ∈ nativeLieLowerCentralModel (I := I) (G := G) k ↔
          v i ∈ nativeLieLowerCentralModel (I := 𝓘(ℝ, F)) (G := Q) k := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
  letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
  letI := nativeCentralSubspaceQuotient_simplyConnected (I := I) V hV
  let Q := G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV
  let J := 𝓘(ℝ, E ⧸ V)
  dsimp only
  intro v hv
  classical
  have hl : ∀ i, ∃ w : E, nativeLieExponential (I := I) (G := G) w ∈ Γ ∧
      finiteRealQuotientProjection V w = v i ∧
      ∀ k ≤ j, w ∈ nativeLieLowerCentralModel (I := I) (G := G) k ↔
        v i ∈ nativeLieLowerCentralModel (I := J) (G := Q) k := by
    intro i
    let T := (Finset.range (j+1)).filter (fun k => v i ∈ nativeLieLowerCentralModel (I := J) (G := Q) k)
    have h0 : 0 ∈ T := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.zero_lt_succ j), ?_⟩
      rw [nativeLieLowerCentralModel_zero]
      exact Submodule.mem_top
    have hT : T.Nonempty := ⟨0, h0⟩
    let d := T.max' hT
    have hd := Finset.mem_filter.mp (Finset.max'_mem T hT)
    have hdj : d ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hd.1)
    obtain ⟨w, hw, hwΓ, hp⟩ := nativeCentralSubspaceQuotient_lie_lattice_layer_lift
      (I := I) Γ V hV d (hprior d hdj) (v i) (hv i) hd.2
    refine ⟨w, hwΓ, hp, ?_⟩
    intro k hk
    constructor
    · intro hwk
      rw [← nativeCentralSubspaceQuotient_lie_layer_image (I := I) V hV k]
      exact ⟨w, hwk, hp⟩
    · intro hvk
      have hkT : k ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk), hvk⟩
      have hkd : k ≤ d := Finset.le_max' T k hkT
      exact nativeLieLowerCentralModel_antitone (I := I) (G := G) hkd hw
  choose u huΓ hup hul using hl
  refine ⟨u, ?_⟩
  intro i
  have hr := nativeSubgroup_logarithm_mem_span (E := E) (I := I) Γ (huΓ i)
  have hr' : u i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
    simpa only [nativeLieGlobalLogarithm_exponential] using hr
  exact ⟨huΓ i, hr', hup i, hul i⟩

end Hindman168
