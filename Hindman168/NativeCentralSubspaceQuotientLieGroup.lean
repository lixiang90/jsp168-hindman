import Hindman168.NativeCentralSubspaceQuotientSmoothLift

/-! Actual original quotient multiplication and inversion are smooth.
Lift both actual quotient arguments smoothly to the original group,
perform its genuine smooth operations, then project through the actual
smooth quotient homomorphism. The proved right-inverse law identifies
these operations with the original quotient group operations. -/

namespace Hindman168
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

theorem nativeCentralSubspaceQuotient_mul_contMDiff :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    let J := 𝓘(ℝ, E ⧸ V)
    ContMDiff (J.prod J) J ∞ (fun p : (G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) × (G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) => p.1 * p.2) := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  let F := E ⧸ V
  let Q := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)
  let J := 𝓘(ℝ, F)
  let q : G →* Q := QuotientGroup.mk' ((nativeCentralSubspaceSubgroup (I := I) V hV))
  let s : Q → G := nativeCentralSubspaceQuotientLift (I := I) V hV
  have hs : ContMDiff J I ∞ s := nativeCentralSubspaceQuotientLift_contMDiff (I := I) V hV
  have h1 : ContMDiff (J.prod J) I ∞ (fun p : Q × Q => s p.1) := hs.comp contMDiff_fst
  have h2 : ContMDiff (J.prod J) I ∞ (fun p : Q × Q => s p.2) := hs.comp contMDiff_snd
  have h : ContMDiff (J.prod J) J ∞ (fun p : Q × Q => q (s p.1 * s p.2)) :=
    (nativeCentralSubspaceQuotient_projection_contMDiff (I := I) V hV).comp (h1.mul h2)
  apply h.congr
  intro p
  symm
  exact (q.map_mul (s p.1) (s p.2)).trans
    (congrArg₂ (fun x y : Q => x * y)
      (nativeCentralSubspaceQuotientLift_right (I := I) V hV p.1)
      (nativeCentralSubspaceQuotientLift_right (I := I) V hV p.2))

theorem nativeCentralSubspaceQuotient_inv_contMDiff :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    let J := 𝓘(ℝ, E ⧸ V)
    ContMDiff J J ∞ (fun x : G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV) => x⁻¹) := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  let F := E ⧸ V
  let Q := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)
  let q : G →* Q := QuotientGroup.mk' ((nativeCentralSubspaceSubgroup (I := I) V hV))
  let s : Q → G := nativeCentralSubspaceQuotientLift (I := I) V hV
  have h : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (fun x : Q => q (s x)⁻¹) :=
    (nativeCentralSubspaceQuotient_projection_contMDiff (I := I) V hV).comp
      (nativeCentralSubspaceQuotientLift_contMDiff (I := I) V hV).inv
  apply h.congr
  intro x
  symm
  exact (q.map_inv (s x)).trans (congrArg (fun y : Q => y⁻¹)
    (nativeCentralSubspaceQuotientLift_right (I := I) V hV x))

theorem nativeCentralSubspaceQuotient_lieGroup :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    LieGroup 𝓘(ℝ, E ⧸ V) ∞ (G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_isManifold (I := I) V hV
  exact { contMDiff_mul := nativeCentralSubspaceQuotient_mul_contMDiff (I := I) V hV
          contMDiff_inv := nativeCentralSubspaceQuotient_inv_contMDiff (I := I) V hV }

end Hindman168
