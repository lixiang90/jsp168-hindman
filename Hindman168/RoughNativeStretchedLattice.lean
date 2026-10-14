import Hindman168.RoughNativeStretchedFiltration
import Hindman168.RoughNativeStretchedLieBracket
import Hindman168.NativeLieLayerLatticeCompact

namespace Hindman168
open Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_stretched_lie_lattice_rational
    (Γ : Subgroup G) [CompactSpace (G ⧸ Γ)] (D i : ℕ) :
    nativeLatticeRationalSubspace (E := E) (I := I) Γ
      (roughNativeStretchedLieFiltration (I := I) (G := G) D i) :=
  nativeLieLowerCentralModel_lattice_rational Γ _

include I in
theorem rough_native_stretched_lattice_quotient_compact
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (D i : ℕ) :
    CompactSpace (roughStretchedLowerCentralFiltration G D i ⧸
      Γ.comap (roughStretchedLowerCentralFiltration G D i).subtype) := by
  rw [rough_native_stretched_filtration_eq (I := I)]
  exact nativeLieLowerCentralLattice_quotient_compact Γ _

include I in
theorem rough_native_stretched_lattice_quotient_closedEmbedding
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (D i : ℕ) :
    Topology.IsClosedEmbedding (subgroupLatticeQuotientInclusion Γ
      (roughStretchedLowerCentralFiltration G D i)) := by
  rw [rough_native_stretched_filtration_eq (I := I)]
  exact nativeLieLowerCentralLattice_quotient_closedEmbedding Γ _

include I in
theorem rough_native_stretched_lattice_orbit_compact
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (D i : ℕ) :
    IsCompact (((↑) : G → G ⧸ Γ) '' (roughStretchedLowerCentralFiltration G D i : Set G)) := by
  rw [rough_native_stretched_filtration_eq (I := I)]
  exact nativeLieLowerCentralLattice_orbit_isCompact Γ _

include I in
theorem rough_native_stretched_lattice_quotient_metrizable
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (D i : ℕ) :
    TopologicalSpace.MetrizableSpace (roughStretchedLowerCentralFiltration G D i ⧸
      Γ.comap (roughStretchedLowerCentralFiltration G D i).subtype) := by
  rw [rough_native_stretched_filtration_eq (I := I)]
  exact nativeLieLowerCentralLattice_quotient_metrizable Γ _

end Hindman168
