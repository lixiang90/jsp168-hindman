import Hindman168.NativeCentralSubspaceQuotientLieGroup

/-! The actual smooth lift preserves identity. Differentiating its genuine
right-inverse law at the original quotient identity gives a genuine right
inverse of the actual original quotient differential, hence surjectivity.
No exact coordinate derivative or bracket comparison is assumed here. -/

namespace Hindman168
open Function
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

variable (V : Submodule ℝ E) [IsClosed (V : Set E)]
  (hV : V ≤ nativeLieCenterModel (I := I) (G := G))

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

theorem nativeCentralSubspaceQuotientLift_one :
    nativeCentralSubspaceQuotientLift (I := I) V hV 1 = 1 := by
  let F := E ⧸ V
  let e : F ≃ₜ (G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) := nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV
  let σ : F →L[ℝ] E := finiteRealQuotientSection V
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  have he : e.symm 1 = 0 :=
    (congrArg e.symm (nativeCentralSubspaceQuotientExponentialHomeomorph_zero (I := I) V hV)).symm.trans
      (e.symm_apply_apply 0)
  have hs : σ (e.symm 1) = 0 := (congrArg σ he).trans σ.map_zero
  exact (congrArg exp hs).trans (nativeLieExponential_zero (I := I) (G := G))

theorem nativeCentralSubspaceQuotient_mfderiv_right :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    let J := 𝓘(ℝ, E ⧸ V)
    let q : G → G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV) := QuotientGroup.mk
    let s : (G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) → G := nativeCentralSubspaceQuotientLift (I := I) V hV
    (mfderiv I J q 1).comp (mfderiv J I s 1) = ContinuousLinearMap.id ℝ _ := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_isManifold (I := I) V hV
  let F := E ⧸ V
  let Q := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)
  let J := 𝓘(ℝ, F)
  let q : G → Q := QuotientGroup.mk
  let s : Q → G := nativeCentralSubspaceQuotientLift (I := I) V hV
  have he : q ∘ s = (id : Q → Q) := funext (nativeCentralSubspaceQuotientLift_right (I := I) V hV)
  have hq : MDifferentiableAt I J q (s 1) :=
    (nativeCentralSubspaceQuotient_projection_contMDiff (I := I) V hV).mdifferentiableAt (by norm_num)
  have hs : MDifferentiableAt J I s 1 :=
    (nativeCentralSubspaceQuotientLift_contMDiff (I := I) V hV).mdifferentiableAt (by norm_num)
  have h := mfderiv_comp (1 : Q) hq hs
  rw [he, mfderiv_id] at h
  have h1 : s (1 : Q) = (1 : G) := nativeCentralSubspaceQuotientLift_one (I := I) V hV
  rw [h1] at h
  exact h.symm

theorem nativeCentralSubspaceQuotient_mfderiv_surjective :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    let J := 𝓘(ℝ, E ⧸ V)
    Surjective (mfderiv I J (QuotientGroup.mk : G → G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) 1) := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  let F := E ⧸ V
  let Q := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)
  let J := 𝓘(ℝ, F)
  let q : G → Q := QuotientGroup.mk
  let s : Q → G := nativeCentralSubspaceQuotientLift (I := I) V hV
  change Surjective (mfderiv I J q (1 : G))
  intro v
  refine ⟨mfderiv J I s 1 v, ?_⟩
  exact congrArg (fun f : F →L[ℝ] F => f v)
    (nativeCentralSubspaceQuotient_mfderiv_right (I := I) V hV)

end Hindman168
