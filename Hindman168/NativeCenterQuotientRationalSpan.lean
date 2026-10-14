import Hindman168.NativeCenterQuotientNativeLogarithm
import Hindman168.NativeSubgroupLogarithmSpan

/-! The actual specified subgroup logarithms commute with the original
center projection. Consequently the original rational logarithmic span
maps exactly onto the actual projected subgroup rational logarithmic
span. This proves neither additivity of nonabelian Log Gamma nor the
remaining central-kernel rational-span equality. -/

namespace Hindman168
open Function Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

omit [Module ℚ E] in
theorem nativeCenterQuotient_logarithm_image (Γ : Subgroup G) :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
    let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
    let Q := G ⧸ Subgroup.center G
    let π : E →L[ℝ] F := nativeCenterQuotientProjection (I := I) (G := G)
    π '' ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) '' (Γ : Set G)) =
      (nativeLieGlobalLogarithm (E := F) (I := 𝓘(ℝ, F)) (G := Q)) ''
        (Γ.map (QuotientGroup.mk' (Subgroup.center G)) : Set Q) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  let J := 𝓘(ℝ, F)
  let q : G →* Q := QuotientGroup.mk' (Subgroup.center G)
  let π : E →L[ℝ] F := nativeCenterQuotientProjection (I := I) (G := G)
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  let logQ : Q → F := nativeLieGlobalLogarithm (E := F) (I := J) (G := Q)
  have he : π ∘ log = logQ ∘ q := funext fun g =>
    (nativeCenterQuotient_nativeLogarithm_projection (I := I) (G := G) g).symm
  change π '' (log '' (Γ : Set G)) = logQ '' (Γ.map q : Set Q)
  rw [Subgroup.coe_map, ← Set.image_comp, ← Set.image_comp, he]

theorem nativeCenterQuotient_rationalLogSpan_map (Γ : Subgroup G) :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
    let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
    (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ).map
      ((nativeCenterQuotientProjection (I := I) (G := G)).toLinearMap.restrictScalars ℚ) =
        nativeSubgroupRationalLogSpan (E := F) (I := 𝓘(ℝ, F)) (Γ.map (QuotientGroup.mk' (Subgroup.center G))) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let π : E →ₗ[ℚ] F := (nativeCenterQuotientProjection (I := I) (G := G)).toLinearMap.restrictScalars ℚ
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  exact (Submodule.map_span π (log '' (Γ : Set G))).trans
    (congrArg (span ℚ) (nativeCenterQuotient_logarithm_image (I := I) (G := G) Γ))

end Hindman168
