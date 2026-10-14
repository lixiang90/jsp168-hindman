import Hindman168.NativeLatticeCentralizer
import Hindman168.NativeLatticeFiniteGeneration
import Hindman168.CenterLatticeCocompactness

/-! The intersection of an arbitrary specified lattice with the actual
original center is a discrete cocompact subgroup of that center. Every
ingredient is derived from the original nilpotent Lie group and original
lattice; no full rational form or compact center quotient is assumed. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

include I

 theorem nativeLattice_center_quotient_compactSpace (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    CompactSpace ((Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G)) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  letI : LocallyCompactSpace G := nativeLieGroup_locallyCompact (E := E) (I := I) (G := G)
  exact center_quotient_compactSpace_of_lattice_centralizer Γ
    (nativeLattice_fg (E := E) (I := I) Γ)
    (nativeLattice_centralizer_eq_center (E := E) (I := I) Γ)

end Hindman168
