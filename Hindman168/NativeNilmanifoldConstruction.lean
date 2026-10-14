import Hindman168.NativeNilmanifoldData
import Hindman168.NilNaturalCosetMetric

/-! Every original native nilmanifold with the specified discrete cocompact
lattice supplies the full recipe data. The compatible metric is constructed,
not required as a new hypothesis. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

variable {E H G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace G] [ChartedSpace H G] [Group G] [IsTopologicalGroup G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G]

noncomputable def nativeNilmanifoldOfLie (s : ℕ) (hs : Group.nilpotencyClass G ≤ s)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] : NativeNilmanifoldData.{u} s := by
  letI : SecondCountableTopology G :=
    (nativeLieGlobalExponentialHomeomorph (E := E) (I := I) (G := G)).symm.secondCountableTopology
  letI : IsClosed (Γ : Set G) := discreteLattice_isClosed Γ
  exact {
    E := E
    H := H
    I := I
    G := G
    step_le := hs
    Γ := Γ
    metric := naturalCompactCosetMetric Γ
    metric_quotientMap := by
      rw [naturalCompactCosetMetric_topology]
      exact QuotientGroup.isOpenQuotientMap_mk }

end Hindman168
