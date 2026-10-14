import Hindman168.NativeGroupLowerCentralExact
import Hindman168.NilLowerCentralGeometry

/-! Original lower-central cube geometry with all restricted-lattice
compactness hypotheses discharged for the arbitrary specified lattice. -/

namespace Hindman168
open Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
include I

theorem native_nilLowerCentral_isClosed (i : ℕ) :
    IsClosed (nilLowerCentralFiltration G i : Set G) :=
  nativeGroupLowerCentralSeries_isClosed (E := E) (I := I) (i - 1)

theorem native_nilLowerCentral_layer_quotient_compact
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : ℕ) :
    CompactSpace ((nilLowerCentralFiltration G i) ⧸
      filtrationLayerLattice (nilLowerCentralFiltration G) Γ i) := by
  change CompactSpace ((⊤ : Subgroup G).lowerCentralSeries (i - 1) ⧸
    Γ.comap ((⊤ : Subgroup G).lowerCentralSeries (i - 1)).subtype)
  rw [nativeGroupLowerCentralSeries_eq_exponential (E := E) (I := I)]
  exact nativeLieLowerCentralLattice_quotient_compact Γ (i - 1)

variable [IsTopologicalGroup G]

theorem native_nilClosedLowerCentralFiltration_eq :
    nilClosedLowerCentralFiltration G = nilLowerCentralFiltration G := by
  funext i
  exact nilClosedLowerCentralFiltration_eq_of_isClosed i
    (native_nilLowerCentral_isClosed (E := E) (I := I) i)

theorem native_nilClosedLowerCentral_layer_quotient_compact
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : ℕ) :
    CompactSpace ((nilClosedLowerCentralFiltration G i) ⧸
      filtrationLayerLattice (nilClosedLowerCentralFiltration G) Γ i) := by
  rw [native_nilClosedLowerCentralFiltration_eq (E := E) (I := I)]
  exact native_nilLowerCentral_layer_quotient_compact (E := E) (I := I) Γ i

theorem native_nilLowerCentral_cube_compact
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (d : ℕ) :
    IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup (nilLowerCentralFiltration G) d)) := by
  letI := nativeLieGroup_locallyCompact (E := E) (I := I) (G := G)
  exact nilLowerCentral_cube_compact_from_layer_quotients Γ QuotientGroup.continuous_mk
    (native_nilLowerCentral_isClosed (E := E) (I := I))
    (native_nilLowerCentral_layer_quotient_compact (E := E) (I := I) Γ)

theorem native_nilClosedLowerCentral_cube_compact
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (d : ℕ) :
    IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup (nilClosedLowerCentralFiltration G) d)) := by
  rw [native_nilClosedLowerCentralFiltration_eq (E := E) (I := I)]
  exact native_nilLowerCentral_cube_compact (E := E) (I := I) Γ d

theorem native_nilClosedLowerCentral_cubeLattice_compact
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (d : ℕ) :
    CompactSpace ((upperFaceCubeGroup (nilClosedLowerCentralFiltration G) d) ⧸
      upperFaceCubeLattice (nilClosedLowerCentralFiltration G) Γ d) := by
  letI := nativeLieGroup_locallyCompact (E := E) (I := I) (G := G)
  exact nilClosedLowerCentral_cubeLattice_compactSpace Γ
    (native_nilClosedLowerCentral_layer_quotient_compact (E := E) (I := I) Γ)

end Hindman168
