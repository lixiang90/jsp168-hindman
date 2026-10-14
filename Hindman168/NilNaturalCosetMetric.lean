import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Metrizable.Uniformity

/-! The actual compact coset space of a closed subgroup is metrizable
with its natural quotient topology, including nonnormal subgroups.
Discrete lattice closedness is derived in a Hausdorff topological group. -/

namespace Hindman168

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem discreteLattice_isClosed [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] :
    IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete

theorem compactClosedCosetQuotient_metrizable [SecondCountableTopology G]
    (Γ : Subgroup G) [IsClosed (Γ : Set G)] [CompactSpace (G ⧸ Γ)] :
    TopologicalSpace.MetrizableSpace (G ⧸ Γ) := by infer_instance

theorem compactDiscreteCosetQuotient_metrizable [T2Space G] [SecondCountableTopology G]
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    TopologicalSpace.MetrizableSpace (G ⧸ Γ) := by
  letI : IsClosed (Γ : Set G) := discreteLattice_isClosed Γ
  exact compactClosedCosetQuotient_metrizable Γ

noncomputable abbrev naturalCompactCosetMetric [SecondCountableTopology G]
    (Γ : Subgroup G) [IsClosed (Γ : Set G)] [CompactSpace (G ⧸ Γ)] : MetricSpace (G ⧸ Γ) :=
  letI := compactClosedCosetQuotient_metrizable Γ
  TopologicalSpace.metrizableSpaceMetric (G ⧸ Γ)

theorem naturalCompactCosetMetric_topology [SecondCountableTopology G]
    (Γ : Subgroup G) [IsClosed (Γ : Set G)] [CompactSpace (G ⧸ Γ)] :
    (naturalCompactCosetMetric Γ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace Γ := by
  with_reducible_and_instances rfl

theorem naturalCompactCosetMetric_continuous_mk [SecondCountableTopology G]
    (Γ : Subgroup G) [IsClosed (Γ : Set G)] [CompactSpace (G ⧸ Γ)] :
    @Continuous G (G ⧸ Γ) inferInstance
      (naturalCompactCosetMetric Γ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      ((↑) : G → G ⧸ Γ) := by
  rw [naturalCompactCosetMetric_topology]
  exact QuotientGroup.continuous_mk

theorem naturalCompactCosetMetric_compactSpace [SecondCountableTopology G]
    (Γ : Subgroup G) [IsClosed (Γ : Set G)] [CompactSpace (G ⧸ Γ)] :
    @CompactSpace (G ⧸ Γ)
      (naturalCompactCosetMetric Γ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  rw [naturalCompactCosetMetric_topology]
  infer_instance

end Hindman168
