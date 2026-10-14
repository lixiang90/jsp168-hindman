import Hindman168.NativeCenterQuotientNormedModel

/-! The genuine original center quotient is Hausdorff in its original
quotient topology, by its proved actual homeomorphism with the actual
separated normed real center-model quotient. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

include I in
theorem nativeCenterQuotient_t2Space : T2Space (G ⧸ Subgroup.center G) :=
  (nativeCenterQuotientExponentialHomeomorph (E := E) (I := I) (G := G)).t2Space

end Hindman168
