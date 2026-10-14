import Hindman168.NativeCenterQuotientHomeomorph
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! Original nontrivial nilpotency forces a nonzero actual real center
model. Thus removing the actual center strictly lowers the original
real model dimension, as required by genuine central induction. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G] [Nontrivial G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeLieCenterModel_finrank_pos :
    0 < Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)) := by
  let V : Submodule ℝ E := nativeLieCenterModel (I := I) (G := G)
  let e : V ≃ₜ Subgroup.center G := nativeLieCenterExponentialHomeomorph (I := I) (G := G)
  obtain ⟨c, hc⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.center_ne_bot G)
  letI : Nontrivial V := ⟨⟨e.symm c, e.symm 1, fun he => hc (e.symm.injective he)⟩⟩
  exact Module.finrank_pos (R := ℝ) (M := V)

theorem nativeCenterQuotientModel_finrank_lt :
    Module.finrank ℝ (E ⧸ nativeLieCenterModel (I := I) (G := G)) < Module.finrank ℝ E := by
  have hp := nativeLieCenterModel_finrank_pos (I := I) (G := G)
  have hr := (nativeLieCenterModel (I := I) (G := G)).finrank_quotient_add_finrank
  omega

end Hindman168
