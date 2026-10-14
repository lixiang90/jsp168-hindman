import Hindman168.UnitriangularLowerCentralExact
import Hindman168.UnitriangularDepthLattice
import Hindman168.NilLowerCentralGeometry

/-! The original lower-central cube compactness route is instantiated for
actual real unitriangular groups and their specified original integer lattice.
Every required layer quotient is now proved, including the zero layer. -/

namespace Hindman168
open Set Topology

variable {n d : ℕ}

 theorem unitriangularFiltration_layer_locallyCompact (i : ℕ) :
    LocallyCompactSpace (unitriangularFiltration n ℝ i) :=
  unitriangularDepth_locallyCompact

 theorem unitriangularFiltration_layer_quotient_compact (i : ℕ) :
    CompactSpace ((unitriangularFiltration n ℝ i) ⧸
      filtrationLayerLattice (unitriangularFiltration n ℝ) (integerUnitriangularLattice n) i) :=
  integerUnitriangularDepthLattice_quotient_compact

 theorem unitriangularFiltration_cube_compact :
    IsCompact (cosetCornerCubeSet (integerUnitriangularLattice n)
      (upperFaceCubeGroup (unitriangularFiltration n ℝ) d)) := by
  apply upperFaceCubeGroup_natural_compact_from_layer_quotients
    (unitriangularFiltration n ℝ) unitriangularFiltration_conditions
  · intro i
    letI := unitriangularFiltration_layer_locallyCompact (n := n) i
    infer_instance
  · exact unitriangularFiltration_layer_quotient_compact

 theorem unitriangular_nilLowerCentral_isClosed (i : ℕ) :
    IsClosed (nilLowerCentralFiltration (Unitriangular n ℝ) i : Set (Unitriangular n ℝ)) := by
  rw [unitriangular_nilLowerCentralFiltration_eq_depth]
  exact unitriangularDepth_isClosed

 theorem unitriangular_nilLowerCentralFiltration_eq :
    nilLowerCentralFiltration (Unitriangular n ℝ) = unitriangularFiltration n ℝ :=
  funext unitriangular_nilLowerCentralFiltration_eq_depth

 theorem unitriangular_nilClosedLowerCentralFiltration_eq :
    nilClosedLowerCentralFiltration (Unitriangular n ℝ) = unitriangularFiltration n ℝ := by
  funext i
  rw [nilClosedLowerCentralFiltration_eq_of_isClosed i (unitriangular_nilLowerCentral_isClosed i)]
  exact unitriangular_nilLowerCentralFiltration_eq_depth i

 theorem unitriangular_nilClosedLowerCentral_layer_quotient_compact (i : ℕ) :
    CompactSpace ((nilClosedLowerCentralFiltration (Unitriangular n ℝ) i) ⧸
      filtrationLayerLattice (nilClosedLowerCentralFiltration (Unitriangular n ℝ))
        (integerUnitriangularLattice n) i) := by
  rw [unitriangular_nilClosedLowerCentralFiltration_eq]
  exact unitriangularFiltration_layer_quotient_compact i

 theorem unitriangular_nilLowerCentral_cube_compact :
    IsCompact (cosetCornerCubeSet (integerUnitriangularLattice n)
      (upperFaceCubeGroup (nilLowerCentralFiltration (Unitriangular n ℝ)) d)) := by
  rw [unitriangular_nilLowerCentralFiltration_eq]
  exact unitriangularFiltration_cube_compact

 theorem unitriangular_nilClosedLowerCentral_cube_compact :
    IsCompact (cosetCornerCubeSet (integerUnitriangularLattice n)
      (upperFaceCubeGroup (nilClosedLowerCentralFiltration (Unitriangular n ℝ)) d)) := by
  rw [unitriangular_nilClosedLowerCentralFiltration_eq]
  exact unitriangularFiltration_cube_compact

 theorem unitriangular_nilClosedLowerCentral_cubeLattice_compact :
    CompactSpace ((upperFaceCubeGroup (nilClosedLowerCentralFiltration (Unitriangular n ℝ)) d) ⧸
      upperFaceCubeLattice (nilClosedLowerCentralFiltration (Unitriangular n ℝ))
        (integerUnitriangularLattice n) d) := by
  letI := unitriangular_locallyCompact (n := n)
  exact nilClosedLowerCentral_cubeLattice_compactSpace (integerUnitriangularLattice n)
    unitriangular_nilClosedLowerCentral_layer_quotient_compact

end Hindman168
