import Hindman168.NativeCentralSubspaceLogLattice
import Hindman168.NativeRationalExponentialSpan
import Hindman168.IntegerLatticeCoordinates

namespace Hindman168
open Submodule Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeCentralSubspaceLogLattice_real_span (Γ : Subgroup G) (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V) :
    span ℝ (nativeCentralSubspaceLogLattice (I := I) Γ V hV : Set V) = ⊤ := by
  apply Submodule.map_injective_of_injective V.subtype_injective
  have he : V.subtype '' (nativeCentralSubspaceLogLattice (I := I) Γ V hV : Set V) =
      {v : E | v ∈ V ∧ nativeLieExponential (I := I) (G := G) v ∈ Γ} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.property, hx⟩
    · rintro ⟨hv, hΓ⟩
      exact ⟨⟨v, hv⟩, hΓ, rfl⟩
  rw [Submodule.map_span, he, Submodule.map_top, Submodule.range_subtype]
  exact nativeRationalSubspace_exponential_span Γ V hrat

theorem nativeCentralSubspaceLogLattice_isZLattice (Γ : Subgroup G) [DiscreteTopology Γ]
    (V : Submodule ℝ E) (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V) :
    letI := nativeCentralSubspaceLogLattice_discrete (I := I) Γ V hV
    IsZLattice ℝ (nativeCentralSubspaceLogLattice (I := I) Γ V hV) := by
  letI := nativeCentralSubspaceLogLattice_discrete (I := I) Γ V hV
  exact ⟨nativeCentralSubspaceLogLattice_real_span Γ V hV hrat⟩

end Hindman168
