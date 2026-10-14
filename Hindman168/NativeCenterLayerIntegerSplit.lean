import Hindman168.IntegerSubspaceSplit
import Hindman168.NativeCenterLatticeCoordinates
import Hindman168.NativeLieLowerCentralModel

/-! Integer splitting for the genuine original central lattice and actual
original lower-central-layer intersections. These are integer module
complements; a simultaneous adapted ordered basis is not yet constructed. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCenterLayerIntegerIntersection (Γ : Subgroup G) (j : ℕ) :
    Submodule ℤ (nativeCenterLogLattice (I := I) Γ) :=
  integerSubspaceIntersection (nativeCenterLogLattice (I := I) Γ)
    ((nativeLieLowerCentralModel (I := I) (G := G) j).comap
      (nativeLieCenterModel (I := I) (G := G)).subtype)

omit [Module ℚ E] [Group.IsNilpotent G] [FiniteDimensional ℝ E]
  [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem native_center_layer_integer_intersection_mem_iff (Γ : Subgroup G) (j : ℕ)
    (x : nativeCenterLogLattice (I := I) Γ) :
    x ∈ nativeCenterLayerIntegerIntersection (I := I) Γ j ↔
      (x.val.val : E) ∈ nativeLieLowerCentralModel (I := I) (G := G) j := Iff.rfl

theorem native_center_layer_integer_quotient_free (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ) :
    Module.Free ℤ ((nativeCenterLogLattice (I := I) Γ) ⧸
      nativeCenterLayerIntegerIntersection (I := I) Γ j) := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  letI : Module.Finite ℤ (nativeCenterLogLattice (I := I) Γ) :=
    Module.Finite.of_basis (integerLatticeIntegerBasis (nativeCenterLogLattice (I := I) Γ))
  exact integer_subspace_quotient_free _ _

theorem native_center_layer_integer_complement_exists (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ) :
    ∃ Q : Submodule ℤ (nativeCenterLogLattice (I := I) Γ),
      IsCompl (nativeCenterLayerIntegerIntersection (I := I) Γ j) Q := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  letI : Module.Finite ℤ (nativeCenterLogLattice (I := I) Γ) :=
    Module.Finite.of_basis (integerLatticeIntegerBasis (nativeCenterLogLattice (I := I) Γ))
  exact integer_subspace_integer_complement_exists _ _

end Hindman168
