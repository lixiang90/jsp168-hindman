import Hindman168.NativeCentralSubspaceQuotientNativeExponential
import Hindman168.NativeOrderedExponentialCoordinates

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

theorem native_ordered_exponential_coordinates_central_subspace_projection
    (V : Submodule ℝ E) [IsClosed (V : Set E)]
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) {m : ℕ} (u : Fin m → E) :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
    letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
    ∀ x : Fin m → ℝ,
      QuotientGroup.mk (nativeOrderedExponentialCoordinates (I := I) (G := G) u x) =
        nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, E ⧸ V))
          (G := G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV)
          (fun i => finiteRealQuotientProjection V (u i)) x := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
  letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
  intro x
  change (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV))
    (nativeOrderedExponentialCoordinates (I := I) (G := G) u x) = _
  simp only [nativeOrderedExponentialCoordinates, map_list_prod, List.map_ofFn, Function.comp_def]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  simpa only [map_smul, QuotientGroup.mk'_apply] using
    nativeCentralSubspaceQuotient_nativeExponential_projection (I := I) V hV (x i • u i)

end Hindman168
