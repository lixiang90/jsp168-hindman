import Hindman168.NativeLieLowerCentralSubgroups

/-! The true original product logarithm is additive modulo the next
native lower-central layer when its second direction belongs to the
current layer. This follows from the actual inverse differential and
genuine Picard integrals, without assuming a BCH comparison. -/

namespace Hindman168
open Function Set MeasureTheory
open scoped Interval Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieLogarithmVectorField_sub_velocity_lowerCentral
    {w : E} {j : ℕ} (hw : w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) (v : E) :
    nativeLieLogarithmVectorField (I := I) (G := G) w v - w ∈
      nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
  let F : E := nativeLieLogarithmVectorField (I := I) (G := G) w v
  let D : E →L[ℝ] E := nativeLieDexp (I := I) (G := G) v
  have hF : F ∈ nativeLieLowerCentralModel (I := I) (G := G) j :=
    nativeLieDexpFiniteInverse_mem_lowerCentral v hw
  have hd : D F = w := nativeLieLogarithmVectorField_dexp w v
  have he : nativeLieDexpDefect (I := I) (G := G) v F = F - w := by
    change (1 - D) F = F - w
    simp only [sub_apply, one_apply_eq_self]
    rw [hd]
  exact he ▸ nativeLieDexpDefect_mem_lowerCentral_next v hF

variable [FiniteDimensional ℝ E]

 theorem nativeLieLogarithmLift_sub_affine_lowerCentral
    {w : E} {j : ℕ} (hw : w ∈ nativeLieLowerCentralModel (I := I) (G := G) j)
    (u : E) (t : ℝ) :
    nativeLieLogarithmLift (E := E) (I := I) (G := G) w u t - (u + t • w) ∈
      nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
  let F : E → E := nativeLieLogarithmVectorField (I := I) (G := G) w
  let q : ℝ → E := continuousPicardIterate F u (Group.nilpotencyClass G)
  have hF : Continuous F := (nativeLieLogarithmVectorField_contDiff w).continuous
  have hq : Continuous q := continuousPicardIterate_continuous hF u _
  have hf : IntervalIntegrable (fun s => F (q s)) volume 0 t :=
    (hF.comp hq).intervalIntegrable 0 t
  have hc : IntervalIntegrable (fun _ : ℝ => w) volume 0 t :=
    continuous_const.intervalIntegrable 0 t
  have he : nativeLieLogarithmLift (E := E) (I := I) (G := G) w u t - (u + t • w) =
      ∫ s in (0 : ℝ)..t, F (q s) - w := by
    rw [intervalIntegral.integral_sub hf hc, intervalIntegral.integral_const, sub_zero]
    change (u + _) - (u + t • w) = _ - t • w
    abel
  rw [he]
  apply nativeLieLowerCentralModel_intervalIntegral_mem (hf.sub hc)
  intro s
  exact nativeLieLogarithmVectorField_sub_velocity_lowerCentral hw (q s)

 theorem nativeLieExponential_product_mem_lowerCentral_next
    {u w : E} {j : ℕ} (hw : w ∈ nativeLieLowerCentralModel (I := I) (G := G) j)
    (hs : u + w ∈ nativeLieLowerCentralModel (I := I) (G := G) (j + 1)) :
    nativeLieExponential (I := I) (G := G) u * nativeLieExponential (I := I) (G := G) w ∈
      nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) (j + 1) := by
  let z : E := nativeLieLogarithmLift (E := E) (I := I) (G := G) w u 1
  have hd : z - (u + w) ∈ nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
    simpa only [one_smul] using nativeLieLogarithmLift_sub_affine_lowerCentral hw u 1
  have hz : z ∈ nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
    simpa only [sub_add_cancel] using
      (nativeLieLowerCentralModel (I := I) (G := G) (j + 1)).add_mem hd hs
  exact ⟨z, hz, nativeLieExponential_product_logarithm (E := E) (I := I) (G := G) u w⟩

end Hindman168
