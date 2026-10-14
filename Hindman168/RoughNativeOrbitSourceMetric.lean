import Hindman168.RoughConjugateOrbitMap
import Hindman168.RoughNativeActionFreezing

namespace Hindman168
open Topology
universe u

@[reducible]
noncomputable def roughNativeOrbitSourceMetric {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (L : Subgroup D.G) (g : D.G) :
    MetricSpace (L ⧸ (roughConjugateSubgroup D.Γ g).comap L.subtype) :=
  MetricSpace.induced (roughConjugateOrbitMap D.Γ L g 1)
    (roughConjugateOrbitMap_injective D.Γ L g 1) D.metric

theorem rough_native_orbit_source_metric_topology {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : Subgroup D.G) (g : D.G)
    [CompactSpace (L ⧸ (roughConjugateSubgroup D.Γ g).comap L.subtype)] :
    QuotientGroup.instTopologicalSpace ((roughConjugateSubgroup D.Γ g).comap L.subtype) =
      (roughNativeOrbitSourceMetric D L g).toUniformSpace.toTopologicalSpace := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  let P (t : TopologicalSpace (D.G ⧸ D.Γ)) : Prop :=
    letI := t
    IsClosedEmbedding (roughConjugateOrbitMap D.Γ L g 1)
  have hn : P (QuotientGroup.instTopologicalSpace D.Γ) := by
    letI : TopologicalSpace (D.G ⧸ D.Γ) := QuotientGroup.instTopologicalSpace D.Γ
    exact roughConjugateOrbitMap_closedEmbedding D.Γ L g 1
  have he := Eq.mp (congrArg P (nativeNilmanifold_metric_topology D)) hn
  exact he.isEmbedding.eq_induced

theorem rough_native_orbit_source_metric_compact {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : Subgroup D.G) (g : D.G)
    [CompactSpace (L ⧸ (roughConjugateSubgroup D.Γ g).comap L.subtype)] :
    letI := roughNativeOrbitSourceMetric D L g
    letI : TopologicalSpace (L ⧸ (roughConjugateSubgroup D.Γ g).comap L.subtype) :=
      (roughNativeOrbitSourceMetric D L g).toUniformSpace.toTopologicalSpace
    CompactSpace (L ⧸ (roughConjugateSubgroup D.Γ g).comap L.subtype) := by
  exact Eq.mp (congrArg (fun t => @CompactSpace _ t)
    (rough_native_orbit_source_metric_topology D L g)) inferInstance

end Hindman168
