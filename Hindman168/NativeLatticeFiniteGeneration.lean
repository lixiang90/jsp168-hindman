import Hindman168.NativeLieExponentialDiffeomorph
import Hindman168.CocompactDiscreteSubgroupFiniteGeneration
import Mathlib.Topology.Homeomorph.Lemmas

/-! Finite generation for the actual specified lattice in the original
arbitrary connected simply connected nilpotent Lie group. Local compactness
is derived from the true original exponential diffeomorphism and original
finite-dimensional real model, not supplied as another hypothesis. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

include I

 theorem nativeLieGroup_locallyCompact : LocallyCompactSpace G :=
  (nativeLieExponentialDiffeomorph (E := E) (I := I) (G := G)).toHomeomorph.locallyCompactSpace_iff.mp
    inferInstance

 theorem nativeLattice_fg (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] : Γ.FG := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  letI : LocallyCompactSpace G := nativeLieGroup_locallyCompact (E := E) (I := I) (G := G)
  exact discreteCocompactSubgroup_fg Γ

end Hindman168
