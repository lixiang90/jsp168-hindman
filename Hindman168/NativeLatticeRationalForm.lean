import Hindman168.NativeLatticeRationalDimension
import Hindman168.NativeLatticeRealSpanning
import Hindman168.RationalSubspaceScalarExtension

/-! The rational form determined by the ORIGINAL specified lattice is
now constructed. Its rational basis has exactly the SAME columns as a
real basis of the original model. The actual natural scalar extension
r tensor w -> r*w is proved bijective, not assumed. -/

namespace Hindman168
open Module
open scoped Manifold ContDiff TensorProduct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLatticeRationalBasis (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Basis (Fin (Module.finrank ℝ E)) ℚ (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rationalSubspaceBasis _ (nativeLattice_rationalLogSpan_finrank (E := E) (I := I) Γ)

noncomputable def nativeLatticeRealBasis (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Basis (Fin (Module.finrank ℝ E)) ℝ E := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rationalSubspaceRealBasis _
    (nativeLattice_rationalLogSpan_finrank (E := E) (I := I) Γ)
    (nativeSubgroupRationalLogSpan_real_span_eq_top (E := E) (I := I) Γ)

 theorem nativeLatticeRealBasis_apply (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : Fin (Module.finrank ℝ E)) :
    nativeLatticeRealBasis (E := E) (I := I) Γ i =
      (nativeLatticeRationalBasis (E := E) (I := I) Γ i : E) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rationalSubspaceRealBasis_apply _ _ _ i

 theorem nativeLatticeRationalBasis_rational_span (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Submodule.span ℚ (Set.range (fun i => (nativeLatticeRationalBasis (E := E) (I := I) Γ i : E))) =
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rationalSubspaceBasis_rational_span _ _

 theorem nativeLatticeRationalBasis_real_linearIndependent (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    LinearIndependent ℝ (fun i => (nativeLatticeRationalBasis (E := E) (I := I) Γ i : E)) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rationalSubspaceBasis_real_linearIndependent _ _
    (nativeSubgroupRationalLogSpan_real_span_eq_top (E := E) (I := I) Γ)

 theorem nativeLatticeRealBasis_mem_rationalLogSpan (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : Fin (Module.finrank ℝ E)) :
    nativeLatticeRealBasis (E := E) (I := I) Γ i ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
  rw [nativeLatticeRealBasis_apply]
  exact (nativeLatticeRationalBasis (E := E) (I := I) Γ i).property

noncomputable def nativeLatticeRationalScalarExtensionEquiv (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    (ℝ ⊗[ℚ] nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) ≃ₗ[ℝ] E := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rationalSubspaceScalarExtensionEquiv _
    (nativeLattice_rationalLogSpan_finrank (E := E) (I := I) Γ)
    (nativeSubgroupRationalLogSpan_real_span_eq_top (E := E) (I := I) Γ)

 theorem nativeLatticeRationalScalarExtensionEquiv_toLinearMap (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    (nativeLatticeRationalScalarExtensionEquiv (E := E) (I := I) Γ).toLinearMap =
      rationalSubspaceScalarExtensionMap (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rationalSubspaceScalarExtensionEquiv_toLinearMap _ _ _

 theorem nativeLatticeRationalScalarExtensionEquiv_tmul (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (r : ℝ)
    (w : nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) :
    nativeLatticeRationalScalarExtensionEquiv (E := E) (I := I) Γ (r ⊗ₜ[ℚ] w) =
      r • (w : E) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rationalSubspaceScalarExtensionEquiv_tmul _ _ _ r w

 theorem nativeLatticeRationalScalarExtensionMap_bijective (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Function.Bijective
      (rationalSubspaceScalarExtensionMap (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rationalSubspaceScalarExtensionMap_bijective _
    (nativeLattice_rationalLogSpan_finrank (E := E) (I := I) Γ)
    (nativeSubgroupRationalLogSpan_real_span_eq_top (E := E) (I := I) Γ)

end Hindman168
