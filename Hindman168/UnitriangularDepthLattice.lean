import Hindman168.UnitriangularDepthCoordinates
import Hindman168.UnitriangularIntegerLattice
import Hindman168.NilNaturalCosetMetric
import Hindman168.SubgroupLatticeQuotient

/-! Compact quotients of every actual superdiagonal layer by its intersection
with the original integer matrix lattice. This is not an identification with
arbitrary nilpotent group or Lie-algebra lower-central layers. -/

namespace Hindman168
open Matrix Set Topology

variable {n k : ℕ}

 def integerUnitriangularDepthLattice (n k : ℕ) :
    Subgroup (unitriangularDepthSubgroup n k ℝ) :=
  (integerUnitriangularLattice n).comap (unitriangularDepthSubgroup n k ℝ).subtype

 noncomputable def unitriangularDepthTransvection (p : UnitriangularDepthIndex n k) (z : ℤ) :
    unitriangularDepthSubgroup n k ℝ :=
  ⟨unitriangularTransvection (unitriangularRow p.val) (unitriangularColumn p.val)
    p.val.property (z : ℝ), unitriangularDepth_transvection k _ _ p.val.property p.property _⟩

 theorem integerUnitriangularDepthLattice_transvection (p : UnitriangularDepthIndex n k)
    (z : ℤ) : unitriangularDepthTransvection p z ∈ integerUnitriangularDepthLattice n k := by
  exact integerUnitriangularLattice_transvection p.val z

 theorem unitriangularDepth_rightTransvection_pivot (g : unitriangularDepthSubgroup n k ℝ)
    (p : UnitriangularDepthIndex n k) (z : ℤ) :
    unitriangularDepthCoordinates (g * unitriangularDepthTransvection p z) p =
      unitriangularDepthCoordinates g p + (z : ℝ) := by
  exact unitriangular_rightTransvection_pivot g.val p.val z

 theorem unitriangularDepth_rightTransvection_earlier (g : unitriangularDepthSubgroup n k ℝ)
    (p : UnitriangularDepthIndex n k) (z : ℤ) (q : UnitriangularDepthIndex n k) (hqp : q < p) :
    unitriangularDepthCoordinates (g * unitriangularDepthTransvection p z) q =
      unitriangularDepthCoordinates g q := by
  exact unitriangular_rightTransvection_earlier g.val p.val z q.val hqp

 theorem integerUnitriangularDepthLattice_representatives (g : unitriangularDepthSubgroup n k ℝ) :
    ∃ x γ, γ ∈ integerUnitriangularDepthLattice n k ∧ g = x * γ ∧
      ∀ p, unitriangularDepthCoordinates x p ∈ Ico 0 1 := by
  exact triangularCoordinates_ordered_reduction (integerUnitriangularDepthLattice n k)
    unitriangularDepthCoordinates unitriangularDepthTransvection
    integerUnitriangularDepthLattice_transvection
    unitriangularDepth_rightTransvection_earlier unitriangularDepth_rightTransvection_pivot g

 theorem integerUnitriangularDepthLattice_quotient_compact :
    CompactSpace (unitriangularDepthSubgroup n k ℝ ⧸ integerUnitriangularDepthLattice n k) := by
  exact triangularCoordinates_compact_quotient (integerUnitriangularDepthLattice n k)
    unitriangularDepthCoordinatesHomeomorph unitriangularDepthTransvection
    integerUnitriangularDepthLattice_transvection
    unitriangularDepth_rightTransvection_earlier unitriangularDepth_rightTransvection_pivot

 theorem unitriangular_locallyCompact : LocallyCompactSpace (Unitriangular n ℝ) :=
  (unitriangularCoordinatesHomeomorph (n := n) (R := ℝ)).isClosedEmbedding.locallyCompactSpace

 theorem unitriangular_secondCountable : SecondCountableTopology (Unitriangular n ℝ) :=
  (unitriangularCoordinatesHomeomorph (n := n) (R := ℝ)).secondCountableTopology

 theorem unitriangularDepth_locallyCompact :
    LocallyCompactSpace (unitriangularDepthSubgroup n k ℝ) :=
  (unitriangularDepthCoordinatesHomeomorph (n := n) (k := k) (R := ℝ)).isClosedEmbedding.locallyCompactSpace

 theorem unitriangularDepth_secondCountable :
    SecondCountableTopology (unitriangularDepthSubgroup n k ℝ) :=
  (unitriangularDepthCoordinatesHomeomorph (n := n) (k := k) (R := ℝ)).secondCountableTopology

 theorem integerUnitriangularDepthLattice_discrete :
    DiscreteTopology (integerUnitriangularDepthLattice n k) := by
  letI := integerUnitriangularLattice_discrete (n := n)
  let f : integerUnitriangularDepthLattice n k → integerUnitriangularLattice n :=
    fun g => ⟨g.val.val, g.property⟩
  have h1 : IsEmbedding ((↑) : integerUnitriangularDepthLattice n k →
      unitriangularDepthSubgroup n k ℝ) := IsEmbedding.subtypeVal
  have h2 : IsEmbedding ((↑) : unitriangularDepthSubgroup n k ℝ →
      Unitriangular n ℝ) := IsEmbedding.subtypeVal
  have h3 : IsEmbedding ((↑) : integerUnitriangularLattice n →
      Unitriangular n ℝ) := IsEmbedding.subtypeVal
  have hf : IsEmbedding f := h3.of_comp_iff.mp (h2.comp h1)
  exact hf.discreteTopology

 theorem integerUnitriangularLattice_isClosed :
    IsClosed (integerUnitriangularLattice n : Set (Unitriangular n ℝ)) := by
  letI := integerUnitriangularLattice_discrete (n := n)
  exact discreteLattice_isClosed _

 theorem integerUnitriangularDepthLattice_isClosed :
    IsClosed (integerUnitriangularDepthLattice n k : Set (unitriangularDepthSubgroup n k ℝ)) := by
  exact (integerUnitriangularLattice_isClosed (n := n)).preimage continuous_subtype_val

 theorem integerUnitriangularLattice_quotient_metrizable :
    TopologicalSpace.MetrizableSpace (Unitriangular n ℝ ⧸ integerUnitriangularLattice n) := by
  letI := unitriangular_secondCountable (n := n)
  letI := integerUnitriangularLattice_isClosed (n := n)
  letI := integerUnitriangularLattice_quotient_compact (n := n)
  exact compactClosedCosetQuotient_metrizable _

 theorem integerUnitriangularDepthLattice_quotient_metrizable :
    TopologicalSpace.MetrizableSpace
      (unitriangularDepthSubgroup n k ℝ ⧸ integerUnitriangularDepthLattice n k) := by
  letI := unitriangularDepth_secondCountable (n := n) (k := k)
  letI := integerUnitriangularDepthLattice_isClosed (n := n) (k := k)
  letI := integerUnitriangularDepthLattice_quotient_compact (n := n) (k := k)
  exact compactClosedCosetQuotient_metrizable _

 theorem integerUnitriangularDepthLattice_quotient_closedEmbedding :
    IsClosedEmbedding (subgroupLatticeQuotientInclusion (integerUnitriangularLattice n)
      (unitriangularDepthSubgroup n k ℝ)) := by
  letI := integerUnitriangularLattice_isClosed (n := n)
  letI : CompactSpace (unitriangularDepthSubgroup n k ℝ ⧸
      (integerUnitriangularLattice n).comap (unitriangularDepthSubgroup n k ℝ).subtype) :=
    integerUnitriangularDepthLattice_quotient_compact (n := n) (k := k)
  exact subgroupLatticeQuotientInclusion_closedEmbedding _ _

 theorem integerUnitriangularDepthLattice_orbit_isCompact :
    IsCompact (((↑) : Unitriangular n ℝ → Unitriangular n ℝ ⧸ integerUnitriangularLattice n) ''
      (unitriangularDepthSubgroup n k ℝ : Set (Unitriangular n ℝ))) := by
  letI : CompactSpace (unitriangularDepthSubgroup n k ℝ ⧸
      (integerUnitriangularLattice n).comap (unitriangularDepthSubgroup n k ℝ).subtype) :=
    integerUnitriangularDepthLattice_quotient_compact (n := n) (k := k)
  exact subgroupLatticeOrbit_isCompact _ _

end Hindman168
