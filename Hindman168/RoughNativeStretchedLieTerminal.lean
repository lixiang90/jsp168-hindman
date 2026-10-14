import Hindman168.RoughNativeStretchedLieBracket

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_stretched_lie_terminal (D : ℕ) (hD : 0 < D)
    {s : ℕ} (hs : Group.nilpotencyClass G ≤ s) :
    roughNativeStretchedLieFiltration (I := I) (G := G) D (s*D+1) = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  have hc := rough_ceiling_index_terminal D hD s
  have hi : Group.nilpotencyClass G ≤ ((s*D+1) ⌈/⌉ D)-1 := by omega
  have hm := nativeLieLowerCentralModel_antitone (I := I) (G := G) hi hv
  rw [nativeLieLowerCentralModel_nilpotencyClass_bot] at hm
  exact hm

theorem rough_native_stretched_lie_beyond_terminal (D : ℕ) (hD : 0 < D)
    {s i : ℕ} (hs : Group.nilpotencyClass G ≤ s) (hi : s*D+1 ≤ i) :
    roughNativeStretchedLieFiltration (I := I) (G := G) D i = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← rough_native_stretched_lie_terminal (I := I) (G := G) D hD hs]
  exact rough_native_stretched_lie_antitone D hD hi

end Hindman168
