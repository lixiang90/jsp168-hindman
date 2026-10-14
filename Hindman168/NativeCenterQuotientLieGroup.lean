import Hindman168.NativeCenterQuotientSmoothLift

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

attribute [local instance] lieGroup_smooth_min_three

theorem nativeCenterQuotient_mul_contMDiff :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    let J := 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G))
    ContMDiff (J.prod J) J ∞ (fun p : (G ⧸ Subgroup.center G) × (G ⧸ Subgroup.center G) => p.1 * p.2) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  let J := 𝓘(ℝ, F)
  let q : G →* Q := QuotientGroup.mk' (Subgroup.center G)
  let s : Q → G := nativeCenterQuotientLift (I := I) (G := G)
  have hs : ContMDiff J I ∞ s := nativeCenterQuotientLift_contMDiff (I := I) (G := G)
  have h1 : ContMDiff (J.prod J) I ∞ (fun p : Q × Q => s p.1) := hs.comp contMDiff_fst
  have h2 : ContMDiff (J.prod J) I ∞ (fun p : Q × Q => s p.2) := hs.comp contMDiff_snd
  have h : ContMDiff (J.prod J) J ∞ (fun p : Q × Q => q (s p.1 * s p.2)) :=
    (nativeCenterQuotient_projection_contMDiff (I := I) (G := G)).comp (h1.mul h2)
  apply h.congr
  intro p
  symm
  exact (q.map_mul (s p.1) (s p.2)).trans
    (congrArg₂ (fun x y : Q => x * y)
      (nativeCenterQuotientLift_right (I := I) (G := G) p.1)
      (nativeCenterQuotientLift_right (I := I) (G := G) p.2))

theorem nativeCenterQuotient_inv_contMDiff :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    let J := 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G))
    ContMDiff J J ∞ (fun x : G ⧸ Subgroup.center G => x⁻¹) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  let q : G →* Q := QuotientGroup.mk' (Subgroup.center G)
  let s : Q → G := nativeCenterQuotientLift (I := I) (G := G)
  have h : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (fun x : Q => q (s x)⁻¹) :=
    (nativeCenterQuotient_projection_contMDiff (I := I) (G := G)).comp
      (nativeCenterQuotientLift_contMDiff (I := I) (G := G)).inv
  apply h.congr
  intro x
  symm
  exact (q.map_inv (s x)).trans (congrArg (fun y : Q => y⁻¹)
    (nativeCenterQuotientLift_right (I := I) (G := G) x))

theorem nativeCenterQuotient_lieGroup :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    LieGroup 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G)) ∞ (G ⧸ Subgroup.center G) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_isManifold (I := I) (G := G)
  exact { contMDiff_mul := nativeCenterQuotient_mul_contMDiff (I := I) (G := G)
          contMDiff_inv := nativeCenterQuotient_inv_contMDiff (I := I) (G := G) }

end Hindman168
