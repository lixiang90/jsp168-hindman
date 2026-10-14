import Hindman168.RationalSubspaceIntersectionSpan
import Hindman168.NativeRationalExponentialSpan
import Hindman168.NativeCenterRationalInclusion

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeLatticeRationalSubspace_inf (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (V T : Submodule ℝ E)
    (hV : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)
    (hT : nativeLatticeRationalSubspace (E := E) (I := I) Γ T) :
    nativeLatticeRationalSubspace (E := E) (I := I) Γ (V ⊓ T) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rationalSubspace_rational_intersection _
    (nativeLattice_rationalLogSpan_finrank (E := E) (I := I) Γ)
    (nativeSubgroupRationalLogSpan_real_span_eq_top (E := E) (I := I) Γ) V T hV hT

theorem nativeLieCenterModel_lattice_rational (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    nativeLatticeRationalSubspace (E := E) (I := I) Γ
      (nativeLieCenterModel (I := I) (G := G)) := by
  apply le_antisymm
  · exact span_le.mpr (fun _ hv => hv.1)
  · have hs := nativeCenter_lattice_logarithms_real_span_eq (E := E) (I := I) Γ
    calc
      _ = span ℝ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) ''
        (Γ ⊓ Subgroup.center G : Subgroup G)) := hs.symm
      _ ≤ _ := span_mono (by
        rintro v ⟨g, hg, rfl⟩
        exact ⟨(nativeLieGlobalLogarithm_mem_centerModel_iff (I := I) (G := G) g).mpr hg.2,
          nativeSubgroup_logarithm_mem_span Γ hg.1⟩)

theorem native_center_layer_integer_real_span (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ) :
    span ℝ (((nativeCenterLogLattice (I := I) Γ ⊓
      ((nativeLieLowerCentralModel (I := I) (G := G) j).comap
        (nativeLieCenterModel (I := I) (G := G)).subtype).restrictScalars ℤ :
          Submodule ℤ (nativeLieCenterModel (I := I) (G := G))) :
            Set (nativeLieCenterModel (I := I) (G := G)))) =
      (nativeLieLowerCentralModel (I := I) (G := G) j).comap
        (nativeLieCenterModel (I := I) (G := G)).subtype := by
  let C := nativeLieCenterModel (I := I) (G := G)
  let V := nativeLieLowerCentralModel (I := I) (G := G) j
  let L := nativeCenterLogLattice (I := I) Γ
  have he : C.subtype '' ((L ⊓ (V.comap C.subtype).restrictScalars ℤ : Submodule ℤ C) : Set C) =
      {v : E | v ∈ C ⊓ V ∧ nativeLieExponential (I := I) (G := G) v ∈ Γ} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.property, hx.2⟩, hx.1⟩
    · rintro ⟨⟨hc, hv⟩, hΓ⟩
      exact ⟨⟨v, hc⟩, ⟨hΓ, hv⟩, rfl⟩
  apply Submodule.map_injective_of_injective C.subtype_injective
  rw [Submodule.map_span, he, Submodule.map_comap_subtype]
  exact nativeRationalSubspace_exponential_span Γ (C ⊓ V)
    (nativeLatticeRationalSubspace_inf Γ C V (nativeLieCenterModel_lattice_rational Γ)
      (nativeLieLowerCentralModel_lattice_rational Γ j))

end Hindman168
