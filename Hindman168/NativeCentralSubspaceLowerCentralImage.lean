import Hindman168.NativeCentralSubspaceQuotientNativeLogarithm
import Hindman168.NativeGroupLowerCentralExact

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

omit [Module ℚ E] in
theorem nativeCentralSubspaceQuotient_group_layer_image (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) (j : ℕ) :
    ((⊤ : Subgroup G).lowerCentralSeries j).map
      (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV)) =
      (⊤ : Subgroup (G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV)).lowerCentralSeries j := by
  rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective _)]

theorem nativeCentralSubspaceQuotient_lie_layer_image (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) (j : ℕ) :
    letI : IsClosed (V : Set E) := V.closed_of_finiteDimensional
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
    letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
    letI := nativeCentralSubspaceQuotient_simplyConnected (I := I) V hV
    (nativeLieLowerCentralModel (I := I) (G := G) j).map V.mkQ =
      nativeLieLowerCentralModel (I := 𝓘(ℝ, E ⧸ V))
        (G := G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV) j := by
  letI : IsClosed (V : Set E) := V.closed_of_finiteDimensional
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
  letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
  letI := nativeCentralSubspaceQuotient_simplyConnected (I := I) V hV
  let Q := G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV
  let J := 𝓘(ℝ, E ⧸ V)
  let q : G →* Q := QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV)
  have himage := nativeCentralSubspaceQuotient_group_layer_image (I := I) V hV j
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hg : nativeLieExponential (I := I) (G := G) v ∈
        (⊤ : Subgroup G).lowerCentralSeries j := by
      rw [nativeGroupLowerCentralSeries_eq_exponential (E := E) (I := I)]
      exact ⟨v, hv, rfl⟩
    have hq : q (nativeLieExponential (I := I) (G := G) v) ∈
        (⊤ : Subgroup Q).lowerCentralSeries j := himage ▸ ⟨_, hg, rfl⟩
    rw [nativeGroupLowerCentralSeries_eq_exponential (E := E ⧸ V) (I := J)] at hq
    obtain ⟨w, hw, he⟩ := hq
    have heq := nativeCentralSubspaceQuotient_nativeExponential_projection (I := I) V hV v
    have hwv : w = V.mkQ v :=
      (nativeLieExponential_injective (I := J) (G := Q)) (he.trans heq)
    exact hwv ▸ hw
  · intro hy
    have hq : nativeLieExponential (I := J) (G := Q) y ∈
        (⊤ : Subgroup Q).lowerCentralSeries j := by
      rw [nativeGroupLowerCentralSeries_eq_exponential (E := E ⧸ V) (I := J)]
      exact ⟨y, hy, rfl⟩
    rw [← himage] at hq
    obtain ⟨g, hg, he⟩ := hq
    rw [nativeGroupLowerCentralSeries_eq_exponential (E := E) (I := I)] at hg
    obtain ⟨v, hv, rfl⟩ := hg
    have heq := nativeCentralSubspaceQuotient_nativeExponential_projection (I := I) V hV v
    have hvy : V.mkQ v = y :=
      (nativeLieExponential_injective (I := J) (G := Q)) (heq.symm.trans he)
    exact ⟨v, hv, hvy⟩

end Hindman168
