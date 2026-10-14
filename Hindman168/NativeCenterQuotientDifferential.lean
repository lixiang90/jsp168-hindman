import Hindman168.NativeCenterQuotientLieGroup

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

attribute [local instance] lieGroup_smooth_min_three

theorem nativeCenterQuotientLift_one :
    nativeCenterQuotientLift (I := I) (G := G) 1 = 1 := by
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let e : F ≃ₜ (G ⧸ Subgroup.center G) := nativeCenterQuotientExponentialHomeomorph (I := I) (G := G)
  let σ : F →L[ℝ] E := nativeCenterQuotientSection (I := I) (G := G)
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  have he : e.symm 1 = 0 :=
    (congrArg e.symm (nativeCenterQuotientExponentialHomeomorph_zero (I := I) (G := G))).symm.trans
      (e.symm_apply_apply 0)
  have hs : σ (e.symm 1) = 0 := (congrArg σ he).trans σ.map_zero
  exact (congrArg exp hs).trans (nativeLieExponential_zero (I := I) (G := G))

theorem nativeCenterQuotient_mfderiv_right :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    let J := 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G))
    let q : G → G ⧸ Subgroup.center G := QuotientGroup.mk
    let s : (G ⧸ Subgroup.center G) → G := nativeCenterQuotientLift (I := I) (G := G)
    (mfderiv I J q 1).comp (mfderiv J I s 1) = ContinuousLinearMap.id ℝ _ := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_isManifold (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  let J := 𝓘(ℝ, F)
  let q : G → Q := QuotientGroup.mk
  let s : Q → G := nativeCenterQuotientLift (I := I) (G := G)
  have he : q ∘ s = (id : Q → Q) := funext (nativeCenterQuotientLift_right (I := I) (G := G))
  have hq : MDifferentiableAt I J q (s 1) :=
    (nativeCenterQuotient_projection_contMDiff (I := I) (G := G)).mdifferentiableAt (by norm_num)
  have hs : MDifferentiableAt J I s 1 :=
    (nativeCenterQuotientLift_contMDiff (I := I) (G := G)).mdifferentiableAt (by norm_num)
  have h := mfderiv_comp (1 : Q) hq hs
  rw [he, mfderiv_id] at h
  have h1 : s (1 : Q) = (1 : G) := nativeCenterQuotientLift_one (I := I) (G := G)
  rw [h1] at h
  exact h.symm

theorem nativeCenterQuotient_mfderiv_surjective :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    let J := 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G))
    Surjective (mfderiv I J (QuotientGroup.mk : G → G ⧸ Subgroup.center G) 1) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  let J := 𝓘(ℝ, F)
  let q : G → Q := QuotientGroup.mk
  let s : Q → G := nativeCenterQuotientLift (I := I) (G := G)
  change Surjective (mfderiv I J q (1 : G))
  intro v
  refine ⟨mfderiv J I s 1 v, ?_⟩
  exact congrArg (fun f : F →L[ℝ] F => f v)
    (nativeCenterQuotient_mfderiv_right (I := I) (G := G))

end Hindman168
