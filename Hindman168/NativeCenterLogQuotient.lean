import Hindman168.NativeCenterLogLattice
import Hindman168.NativeCenterLattice

/-! The true center logarithm descends from the natural original center
coset quotient to its actual additive logarithmic lattice quotient.
Actual continuity and surjectivity transfer original proved compactness. -/

namespace Hindman168
open Function Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCenterQuotientLogarithm (Γ : Subgroup G) :
    (Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G) →
      nativeLieCenterModel (I := I) (G := G) ⧸ nativeCenterLogLattice (I := I) Γ :=
  Quotient.lift (fun g : Subgroup.center G => Submodule.Quotient.mk
    ((nativeLieCenterExponentialHomeomorph (I := I) (G := G)).symm g)) (by
      intro a b hab
      let e := nativeLieCenterExponentialHomeomorph (I := I) (G := G)
      have hz : a⁻¹ * b ∈ Γ.subgroupOf (Subgroup.center G) :=
        QuotientGroup.leftRel_apply.mp hab
      have hlz : e.symm (a⁻¹ * b) ∈ nativeCenterLogLattice (I := I) Γ :=
        (nativeCenterLogLattice_logarithm_mem_iff Γ (a⁻¹ * b)).mpr hz
      have he : e.symm b = e.symm a + e.symm (a⁻¹ * b) := by
        simpa only [mul_inv_cancel_left] using
          nativeLieCenterExponentialHomeomorph_symm_mul (I := I) a (a⁻¹ * b)
      apply (Submodule.Quotient.eq (nativeCenterLogLattice (I := I) Γ)).mpr
      rw [he]
      change e.symm a - (e.symm a + e.symm (a⁻¹ * b)) ∈ _
      simpa only [sub_add_cancel_left] using (nativeCenterLogLattice (I := I) Γ).neg_mem hlz)

 theorem nativeCenterQuotientLogarithm_mk (Γ : Subgroup G) (g : Subgroup.center G) :
    nativeCenterQuotientLogarithm (I := I) Γ (QuotientGroup.mk g) =
      Submodule.Quotient.mk ((nativeLieCenterExponentialHomeomorph (I := I) (G := G)).symm g) := rfl

 theorem nativeCenterQuotientLogarithm_continuous (Γ : Subgroup G) :
    Continuous (nativeCenterQuotientLogarithm (I := I) Γ) := by
  apply (QuotientGroup.isQuotientMap_mk (Γ.subgroupOf (Subgroup.center G))).continuous_iff.mpr
  exact continuous_quot_mk.comp (nativeLieCenterExponentialHomeomorph (I := I) (G := G)).symm.continuous

 theorem nativeCenterQuotientLogarithm_surjective (Γ : Subgroup G) :
    Surjective (nativeCenterQuotientLogarithm (I := I) Γ) := by
  intro x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (nativeCenterLogLattice (I := I) Γ) x
  refine ⟨QuotientGroup.mk (nativeLieCenterExponentialHomeomorph (I := I) (G := G) v), ?_⟩
  rw [nativeCenterQuotientLogarithm_mk, Homeomorph.symm_apply_apply]

variable [Module ℚ E]

 theorem nativeCenterLogLattice_quotient_compactSpace (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    CompactSpace (nativeLieCenterModel (I := I) (G := G) ⧸ nativeCenterLogLattice (I := I) Γ) := by
  letI := nativeLattice_center_quotient_compactSpace (E := E) (I := I) Γ
  have hc := isCompact_range (nativeCenterQuotientLogarithm_continuous (I := I) Γ)
  rw [range_eq_univ.mpr (nativeCenterQuotientLogarithm_surjective (I := I) Γ)] at hc
  exact isCompact_univ_iff.mp hc

end Hindman168
