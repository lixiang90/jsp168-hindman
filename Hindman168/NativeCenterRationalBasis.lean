import Hindman168.NativeCenterLogSpanning
import Hindman168.IntegerLatticeRationalBasis

/-! Actual rational logarithmic coordinates of the original specified
center lattice. The constructed rational basis is real linearly
independent and has size exactly the original real center dimension. -/

namespace Hindman168
open Set Submodule Module
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCenterRationalLogSpan (Γ : Subgroup G) :
    Submodule ℚ (nativeLieCenterModel (I := I) (G := G)) :=
  span ℚ (nativeCenterLogLattice (I := I) Γ : Set (nativeLieCenterModel (I := I) (G := G)))

 theorem nativeCenterRationalLogSpan_finiteDimensional (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    FiniteDimensional ℚ (nativeCenterRationalLogSpan (I := I) Γ) := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  exact integerLatticeRationalSpan_finiteDimensional (nativeCenterLogLattice (I := I) Γ)

 theorem nativeCenterRationalLogSpan_finrank (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Module.finrank ℚ (nativeCenterRationalLogSpan (I := I) Γ) =
      Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)) := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  exact integerLatticeRationalSpan_finrank (nativeCenterLogLattice (I := I) Γ)

 theorem nativeCenterRationalLogSpan_exists_real_independent_basis (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ b : Basis (Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) ℚ
        (nativeCenterRationalLogSpan (I := I) Γ),
      LinearIndependent ℝ (fun i => (b i : nativeLieCenterModel (I := I) (G := G))) := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  exact ⟨integerLatticeRationalBasis (nativeCenterLogLattice (I := I) Γ),
    integerLatticeRationalBasis_real_linearIndependent (nativeCenterLogLattice (I := I) Γ)⟩

end Hindman168
