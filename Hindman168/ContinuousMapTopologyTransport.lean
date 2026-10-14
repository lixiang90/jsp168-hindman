import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Complex.Basic

/-! Actual continuous functions under PROVED equality of topologies,
retaining point values and uniform functionspace metric exactly. -/

namespace Hindman168

noncomputable def continuousMapTopologyTransport (X : Type*) (a b : TopologicalSpace X)
    (h : a=b) (F : @ContinuousMap X ℂ a inferInstance) : @ContinuousMap X ℂ b inferInstance := by
  cases h
  exact F

theorem continuous_map_topology_transport_apply (X : Type*) (a b : TopologicalSpace X)
    (h : a=b) (F : @ContinuousMap X ℂ a inferInstance) (x : X) :
    continuousMapTopologyTransport X a b h F x = F x := by
  cases h
  rfl

theorem continuous_map_topology_transport_isometry (X : Type*) (a b : TopologicalSpace X)
    (h : a=b) (hA : @CompactSpace X a) (hB : @CompactSpace X b) :
    letI : TopologicalSpace X := a
    letI : CompactSpace X := hA
    letI : TopologicalSpace X := b
    letI : CompactSpace X := hB
    Isometry (continuousMapTopologyTransport X a b h) := by
  cases h
  change Isometry (id : @ContinuousMap X ℂ a inferInstance → @ContinuousMap X ℂ a inferInstance)
  exact isometry_id

theorem continuous_map_topology_transport_continuous (X : Type*) (a b : TopologicalSpace X)
    (h : a=b) : Continuous (continuousMapTopologyTransport X a b h) := by
  cases h
  change Continuous (id : @ContinuousMap X ℂ a inferInstance → @ContinuousMap X ℂ a inferInstance)
  exact continuous_id

end Hindman168
