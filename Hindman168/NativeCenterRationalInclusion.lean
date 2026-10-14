import Hindman168.NativeCenterRationalBasis
import Hindman168.NativeSubgroupLogarithmSpan

/-! The actual center logarithmic lattice and rational span are identified
inside the original ambient model. They use the specified actual
Gamma-center intersection and sit inside the original rational log span.
No equality with all central vectors in that larger rational span is assumed. -/

namespace Hindman168
open Function Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

omit [Module ℚ E] in
 theorem nativeCenterLogLattice_image_eq_logarithms (Γ : Subgroup G) :
    ((↑) : nativeLieCenterModel (I := I) (G := G) → E) ''
      (nativeCenterLogLattice (I := I) Γ : Set (nativeLieCenterModel (I := I) (G := G))) =
    (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) ''
      (Γ ⊓ Subgroup.center G : Subgroup G) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨nativeLieExponential (I := I) (G := G) v.val,
      ⟨hv, (nativeLieExponential_mem_center_iff_mem_centerModel v.val).mpr v.property⟩, ?_⟩
    exact nativeLieGlobalLogarithm_exponential (I := I) (G := G) v.val
  · rintro ⟨g, hg, rfl⟩
    let v : nativeLieCenterModel (I := I) (G := G) :=
      ⟨nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g,
        (nativeLieGlobalLogarithm_mem_centerModel_iff g).mpr hg.2⟩
    refine ⟨v, ?_, rfl⟩
    change nativeLieExponential (I := I) (G := G)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) ∈ Γ
    rw [nativeLieExponential_globalLogarithm]
    exact hg.1

 theorem nativeCenterRationalLogSpan_map_eq_original_span (Γ : Subgroup G) :
    (nativeCenterRationalLogSpan (I := I) Γ).map
      ((nativeLieCenterModel (I := I) (G := G)).subtype.restrictScalars ℚ) =
    span ℚ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) ''
      (Γ ⊓ Subgroup.center G : Subgroup G)) := by
  let V : Submodule ℝ E := nativeLieCenterModel (I := I) (G := G)
  let L : Submodule ℤ V := nativeCenterLogLattice (I := I) Γ
  let f : V →ₗ[ℚ] E := V.subtype.restrictScalars ℚ
  change (span ℚ (L : Set V)).map f = _
  exact (Submodule.map_span f (L : Set V)).trans
    (congrArg (span ℚ) (nativeCenterLogLattice_image_eq_logarithms (E := E) (I := I) Γ))

 theorem nativeCenterRationalLogSpan_map_le_original_span (Γ : Subgroup G) :
    (nativeCenterRationalLogSpan (I := I) Γ).map
      ((nativeLieCenterModel (I := I) (G := G)).subtype.restrictScalars ℚ) ≤
        nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
  rw [nativeCenterRationalLogSpan_map_eq_original_span]
  apply span_mono
  exact image_mono (show (Γ ⊓ Subgroup.center G : Subgroup G) ≤ Γ from inf_le_left)

 theorem nativeCenter_lattice_logarithms_real_span_eq (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    span ℝ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) ''
      (Γ ⊓ Subgroup.center G : Subgroup G)) = nativeLieCenterModel (I := I) (G := G) := by
  rw [← nativeCenterLogLattice_image_eq_logarithms (E := E) (I := I) Γ]
  let V : Submodule ℝ E := nativeLieCenterModel (I := I) (G := G)
  let L : Submodule ℤ V := nativeCenterLogLattice (I := I) Γ
  exact (Submodule.map_span V.subtype (L : Set V)).symm.trans
    ((congrArg (Submodule.map V.subtype)
      (nativeCenterLogLattice_real_span_top (E := E) (I := I) Γ)).trans
        (Submodule.map_subtype_top V))

end Hindman168
