import Hindman168.NativeNilmanifoldData
import Hindman168.NativeMetricMaskModelTesting
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Compactness.Lindelof

namespace Hindman168
open Set Topology
open scoped Manifold ContDiff
universe u

theorem native_nilmanifold_group_polish {s : ℕ} (D : NativeNilmanifoldData.{u} s) : PolishSpace D.G :=
  (nativeLieGlobalExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G)).symm.isClosedEmbedding.polishSpace

theorem native_nilmanifold_group_locallyCompact {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    LocallyCompactSpace D.G :=
  (nativeLieGlobalExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G)).symm.isClosedEmbedding.locallyCompactSpace

theorem native_nilmanifold_lattice_countable {s : ℕ} (D : NativeNilmanifoldData.{u} s) : Countable D.Γ := by
  letI : SecondCountableTopology D.G :=
    (nativeLieGlobalExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G)).symm.secondCountableTopology
  exact countable_of_Lindelof_of_discrete

theorem native_nilmanifold_quotient_covering {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    IsCoveringMap ((↑) : D.G → D.G ⧸ D.Γ) :=
  (D.Γ.isQuotientCoveringMap (SetLike.isDiscrete_iff_discreteTopology.mpr D.latticeDiscrete)).isCoveringMap

theorem native_nilmanifold_metric_quotient_covering {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCoveringMap ((↑) : D.G → D.G ⧸ D.Γ) := by
  exact Eq.mp (congrArg (fun t : TopologicalSpace (D.G ⧸ D.Γ) =>
    @IsCoveringMap D.G (D.G ⧸ D.Γ) D.groupTopology t ((↑) : D.G → D.G ⧸ D.Γ))
      (nativeNilmanifold_metric_topology D)) (native_nilmanifold_quotient_covering D)

end Hindman168
