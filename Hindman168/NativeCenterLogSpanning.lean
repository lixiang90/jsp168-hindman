import Hindman168.NativeCenterLogQuotient
import Hindman168.IntegerCocompactRealSpan

/-! The actual logarithms of the specified center lattice span the
entire original real Lie center. This follows from the proved natural
center quotient compactness and actual discrete integer logarithmic
submodule, not from a supplied rational center or spanning premise. -/

namespace Hindman168
open Submodule Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeCenterLogLattice_real_span_top (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    span ℝ (nativeCenterLogLattice (I := I) Γ : Set (nativeLieCenterModel (I := I) (G := G))) = ⊤ := by
  letI := nativeCenterLogLattice_quotient_compactSpace (E := E) (I := I) Γ
  exact integerSubmodule_real_span_top_of_compact_quotient (nativeCenterLogLattice (I := I) Γ)

 theorem nativeCenterLogLattice_isZLattice (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
    IsZLattice ℝ (nativeCenterLogLattice (I := I) Γ) := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  exact ⟨nativeCenterLogLattice_real_span_top (E := E) (I := I) Γ⟩

 theorem nativeCenterLogLattice_integer_rank_eq (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Module.finrank ℤ (nativeCenterLogLattice (I := I) Γ) =
      Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)) := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  exact ZLattice.rank ℝ (nativeCenterLogLattice (I := I) Γ)

end Hindman168
