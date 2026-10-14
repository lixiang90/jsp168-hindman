import Hindman168.NativeLieGroupNilpotency

/-! The actual original native Lie lower central series, viewed in its
original model E. Actual native adjoint generators lower this filtration
by one; a parameter difference in layer j changes their action only in
layer j+1. No substitute Lie algebra or supplied filtration is used. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieLowerCentralModel (j : ℕ) : Submodule ℝ E :=
  (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) j).toSubmodule

omit [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieLowerCentralModel_zero :
    nativeLieLowerCentralModel (I := I) (G := G) 0 = ⊤ := rfl

omit [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieLowerCentralModel_antitone :
    Antitone (nativeLieLowerCentralModel (I := I) (G := G)) := by
  intro j k hjk
  exact LieModule.antitone_lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) hjk

 theorem nativeLieLowerCentralModel_nilpotencyClass_bot [Group.IsNilpotent G] :
    nativeLieLowerCentralModel (I := I) (G := G) (Group.nilpotencyClass G) = ⊥ := by
  unfold nativeLieLowerCentralModel
  rw [nativeLieLowerCentral_nilpotencyClass_bot]
  rfl

 theorem nativeLieAdjointGenerator_mem_lowerCentral_next (v : E) {w : E} {j : ℕ}
    (hw : w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) :
    nativeLieAdjointGenerator (I := I) (G := G) v w ∈
      nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
  let x : GroupLieAlgebra I G := v
  let y : GroupLieAlgebra I G := w
  have hy : y ∈ LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) j := hw
  have hl : ⁅x, y⁆ ∈
      LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) (j + 1) := by
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hy
  exact (nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) x y).symm ▸ hl

 theorem nativeLieAdjointGenerator_pow_mem_lowerCentral (v : E) {w : E} {j : ℕ}
    (hw : w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) (n : ℕ) :
    (nativeLieAdjointGenerator (I := I) (G := G) v ^ n) w ∈
      nativeLieLowerCentralModel (I := I) (G := G) (j + n) := by
  let B : E →L[ℝ] E := nativeLieAdjointGenerator (I := I) (G := G) v
  change (B ^ n) w ∈ nativeLieLowerCentralModel (I := I) (G := G) (j + n)
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self, Nat.add_zero] using hw
  | succ n ih =>
    rw [pow_succ']
    exact nativeLieAdjointGenerator_mem_lowerCentral_next (I := I) (G := G) v ih

 theorem nativeLieAdjointGenerator_pow_mem_lowerCentral_self (v : E) {w : E} {j : ℕ}
    (hw : w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) (n : ℕ) :
    (nativeLieAdjointGenerator (I := I) (G := G) v ^ n) w ∈
      nativeLieLowerCentralModel (I := I) (G := G) j :=
  nativeLieLowerCentralModel_antitone (I := I) (G := G) (Nat.le_add_right j n)
    (nativeLieAdjointGenerator_pow_mem_lowerCentral v hw n)

 theorem nativeLieAdjointGenerator_action_sub_mem_lowerCentral_next {v w : E} {j : ℕ}
    (h : v - w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) (u : E) :
    nativeLieAdjointGenerator (I := I) (G := G) v u -
      nativeLieAdjointGenerator (I := I) (G := G) w u ∈
        nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
  have he : nativeLieAdjointGenerator (I := I) (G := G) v u -
      nativeLieAdjointGenerator (I := I) (G := G) w u =
        -nativeLieAdjointGenerator (I := I) (G := G) u (v - w) := by
    calc
      _ = nativeLieAdjointGenerator (I := I) (G := G) (v - w) u := by
        simp only [nativeLieAdjointGenerator_eq_differential, map_sub,
          sub_apply]
      _ = _ := nativeLieAdjointGenerator_alternating (I := I) (G := G) (v - w) u
  rw [he]
  exact (nativeLieLowerCentralModel (I := I) (G := G) (j + 1)).neg_mem
    (nativeLieAdjointGenerator_mem_lowerCentral_next u h)

end Hindman168
