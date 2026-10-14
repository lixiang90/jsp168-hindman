import Hindman168.NativeRelativeLayerLieSubalgebras
import Hindman168.NativeRationalLatticeCompact

/-! Genuine lattice intersections and compact embedded layer quotients for
every actual internal relative/reduced layer, using their proved rationality. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_internal_layer_lattice_discrete {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    DiscreteTopology ((nativeRelativeSquareData D d hd 1).Γ.comap
      (nativeRelativeSquareInternalFiltration D d i).subtype) := by
  rw [← native_relative_internal_layer_subgroup_eq D d hd i]
  exact nativeLieLattice_intersection_discrete (nativeRelativeSquareData D d hd 1).Γ _

theorem native_relative_reduced_layer_lattice_discrete {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    DiscreteTopology ((nativeRelativeReducedData D d hd).Γ.comap
      (nativeRelativeReducedNativeFiltration D d hd i).subtype) := by
  rw [← native_relative_reduced_layer_subgroup_eq D d hd i]
  exact nativeLieLattice_intersection_discrete (nativeRelativeReducedData D d hd).Γ _

theorem native_relative_internal_layer_lattice_cocompact {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    CompactSpace ((nativeRelativeSquareInternalFiltration D d i) ⧸
      (nativeRelativeSquareData D d hd 1).Γ.comap (nativeRelativeSquareInternalFiltration D d i).subtype) := by
  rw [← native_relative_internal_layer_subgroup_eq D d hd i]
  apply nativeRationalLieLattice_quotient_compact (nativeRelativeSquareData D d hd 1).Γ _
  rw [native_relative_internal_subalgebra_model]
  exact native_relative_lie_layer_rational D d hd i

theorem native_relative_reduced_layer_lattice_cocompact {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    CompactSpace ((nativeRelativeReducedNativeFiltration D d hd i) ⧸
      (nativeRelativeReducedData D d hd).Γ.comap (nativeRelativeReducedNativeFiltration D d hd i).subtype) := by
  rw [← native_relative_reduced_layer_subgroup_eq D d hd i]
  apply nativeRationalLieLattice_quotient_compact (nativeRelativeReducedData D d hd).Γ _
  rw [native_relative_reduced_subalgebra_model]
  exact native_relative_reduced_layer_rational D d hd i

theorem native_relative_internal_layer_quotient_closedEmbedding {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    Topology.IsClosedEmbedding (subgroupLatticeQuotientInclusion (nativeRelativeSquareData D d hd 1).Γ
      (nativeRelativeSquareInternalFiltration D d i)) := by
  rw [← native_relative_internal_layer_subgroup_eq D d hd i]
  apply nativeRationalLieLattice_quotient_closedEmbedding (nativeRelativeSquareData D d hd 1).Γ _
  rw [native_relative_internal_subalgebra_model]
  exact native_relative_lie_layer_rational D d hd i

theorem native_relative_reduced_layer_quotient_closedEmbedding {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    Topology.IsClosedEmbedding (subgroupLatticeQuotientInclusion (nativeRelativeReducedData D d hd).Γ
      (nativeRelativeReducedNativeFiltration D d hd i)) := by
  rw [← native_relative_reduced_layer_subgroup_eq D d hd i]
  apply nativeRationalLieLattice_quotient_closedEmbedding (nativeRelativeReducedData D d hd).Γ _
  rw [native_relative_reduced_subalgebra_model]
  exact native_relative_reduced_layer_rational D d hd i

theorem native_relative_internal_layer_orbit_compact {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    IsCompact (((↑) : (nativeRelativeSquareData D d hd 1).G →
      (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ) ''
        {g : (nativeRelativeSquareData D d hd 1).G | g ∈ nativeRelativeSquareInternalFiltration D d i}) := by
  rw [← native_relative_internal_layer_subgroup_eq D d hd i]
  apply nativeRationalLieLattice_orbit_isCompact (nativeRelativeSquareData D d hd 1).Γ _
  rw [native_relative_internal_subalgebra_model]
  exact native_relative_lie_layer_rational D d hd i

theorem native_relative_reduced_layer_orbit_compact {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    IsCompact (((↑) : (nativeRelativeReducedData D d hd).G →
      (nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) ''
        (nativeRelativeReducedNativeFiltration D d hd i : Set (nativeRelativeReducedData D d hd).G)) := by
  rw [← native_relative_reduced_layer_subgroup_eq D d hd i]
  apply nativeRationalLieLattice_orbit_isCompact (nativeRelativeReducedData D d hd).Γ _
  rw [native_relative_reduced_subalgebra_model]
  exact native_relative_reduced_layer_rational D d hd i

end Hindman168
