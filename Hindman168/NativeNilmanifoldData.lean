import Hindman168.NativeLieGlobalTopology
import Hindman168.ProductLatticeGeometry
import Hindman168.ProductCosetMetric

/-! Full native nilmanifold data, including the original finite-dimensional
model, manifold, specified lattice and compatible metric on the actual coset
space. No matrix replacement or assumed layer compactness is included. -/

namespace Hindman168
open scoped Manifold ContDiff

universe u

structure NativeNilmanifoldData (s : ℕ) where
  E : Type u
  [normedAdd : NormedAddCommGroup E]
  [normedReal : NormedSpace ℝ E]
  [completeModel : CompleteSpace E]
  [rationalModule : Module ℚ E]
  [finiteModel : FiniteDimensional ℝ E]
  H : Type u
  [modelTopology : TopologicalSpace H]
  I : ModelWithCorners ℝ E H
  G : Type u
  [groupTopology : TopologicalSpace G]
  [charted : ChartedSpace H G]
  [group : Group G]
  [topologicalGroup : IsTopologicalGroup G]
  [lie : LieGroup I ∞ G]
  [boundaryless : BoundarylessManifold I G]
  [hausdorff : T2Space G]
  [nilpotent : Group.IsNilpotent G]
  [connected : ConnectedSpace G]
  [simplyConnected : SimplyConnectedSpace G]
  step_le : Group.nilpotencyClass G ≤ s
  Γ : Subgroup G
  [latticeDiscrete : DiscreteTopology Γ]
  [quotientCompact : CompactSpace (G ⧸ Γ)]
  metric : MetricSpace (G ⧸ Γ)
  metric_quotientMap : @IsOpenQuotientMap G (G ⧸ Γ) groupTopology
    metric.toUniformSpace.toTopologicalSpace (↑)

attribute [instance] NativeNilmanifoldData.normedAdd NativeNilmanifoldData.normedReal
  NativeNilmanifoldData.completeModel NativeNilmanifoldData.rationalModule
  NativeNilmanifoldData.finiteModel NativeNilmanifoldData.modelTopology
  NativeNilmanifoldData.groupTopology NativeNilmanifoldData.charted NativeNilmanifoldData.group
  NativeNilmanifoldData.topologicalGroup NativeNilmanifoldData.lie NativeNilmanifoldData.boundaryless
  NativeNilmanifoldData.hausdorff NativeNilmanifoldData.nilpotent NativeNilmanifoldData.connected
  NativeNilmanifoldData.simplyConnected NativeNilmanifoldData.latticeDiscrete NativeNilmanifoldData.quotientCompact

noncomputable def nativeNilmanifoldProduct {s : ℕ} (A B : NativeNilmanifoldData.{u} s) :
    NativeNilmanifoldData.{u} s := by
  letI := nativeLieGroup_contractible (E := A.E) (I := A.I) (G := A.G)
  letI := nativeLieGroup_contractible (E := B.E) (I := B.I) (G := B.G)
  letI := productLattice_discrete A.Γ B.Γ
  letI := productLattice_quotient_compact A.Γ B.Γ
  letI : MetricSpace (A.G ⧸ A.Γ) := A.metric
  letI : MetricSpace (B.G ⧸ B.Γ) := B.metric
  exact {
    E := A.E × B.E
    H := ModelProd A.H B.H
    I := A.I.prod B.I
    G := A.G × B.G
    step_le := productGroup_nilpotencyClass_le s A.step_le B.step_le
    Γ := A.Γ.prod B.Γ
    metric := productCosetMetric A.Γ B.Γ
    metric_quotientMap := productCosetMetric_quotientMap A.Γ B.Γ A.metric_quotientMap B.metric_quotientMap }

end Hindman168
