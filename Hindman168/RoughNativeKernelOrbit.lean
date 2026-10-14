import Hindman168.RoughNativeConjugateLatticeCompact
import Hindman168.RoughConjugateOrbitMap

namespace Hindman168
open Set Submodule Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_residue_kernel_orbit_closedEmbedding (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S))
    (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ, ∃ r : ℚ, F x = (r : ℝ))
    (V : E) (hV : V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) (j : ℤ) (ell : G) :
    IsClosedEmbedding (roughConjugateOrbitMap Γ
      (nativeLieSubalgebraSubgroup (E := E) (nativeLieCharacterKernel S F hF))
      (nativeLieExponential (I := I) (G := G) ((j : ℝ) • V)) ell) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I (minSmoothness ℝ 3)
  letI : IsClosed (Γ : Set G) := discreteLattice_isClosed Γ
  letI := rough_native_residue_kernel_quotient_compact Γ S hS F hF hQ V hV j
  exact roughConjugateOrbitMap_closedEmbedding _ _ _ _

theorem rough_native_residue_kernel_orbit_compact (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S))
    (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ, ∃ r : ℚ, F x = (r : ℝ))
    (V : E) (hV : V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) (j : ℤ) (ell : G) :
    IsCompact (Set.range (roughConjugateOrbitMap Γ
      (nativeLieSubalgebraSubgroup (E := E) (nativeLieCharacterKernel S F hF))
      (nativeLieExponential (I := I) (G := G) ((j : ℝ) • V)) ell)) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I (minSmoothness ℝ 3)
  letI := rough_native_residue_kernel_quotient_compact Γ S hS F hF hQ V hV j
  exact isCompact_range (roughConjugateOrbitMap_continuous _ _ _ _)

end Hindman168
