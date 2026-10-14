import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ProperAction.Basic

/-! The inclusion of a subgroup induces an injective continuous map on its
actual restricted-lattice coset space, including nonnormal lattices. -/

namespace Hindman168
open Set Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

 noncomputable def subgroupLatticeQuotientInclusion (Γ H : Subgroup G) :
    H ⧸ Γ.comap H.subtype → G ⧸ Γ :=
  Quotient.lift (fun x : H => (x.val : G ⧸ Γ)) (fun x y h => by
    apply QuotientGroup.eq.mpr
    have hh : x⁻¹ * y ∈ Γ.comap H.subtype := QuotientGroup.leftRel_apply.mp h
    exact hh)

 omit [TopologicalSpace G] [IsTopologicalGroup G] in
 theorem subgroupLatticeQuotientInclusion_mk (Γ H : Subgroup G) (x : H) :
    subgroupLatticeQuotientInclusion Γ H (x : H ⧸ Γ.comap H.subtype) =
      (x.val : G ⧸ Γ) := rfl

 omit [IsTopologicalGroup G] in
 theorem subgroupLatticeQuotientInclusion_continuous (Γ H : Subgroup G) :
    Continuous (subgroupLatticeQuotientInclusion Γ H) := by
  exact continuous_quot_lift _ (QuotientGroup.continuous_mk.comp continuous_subtype_val)

 omit [TopologicalSpace G] [IsTopologicalGroup G] in
 theorem subgroupLatticeQuotientInclusion_injective (Γ H : Subgroup G) :
    Function.Injective (subgroupLatticeQuotientInclusion Γ H) := by
  intro a b
  induction a, b using Quotient.inductionOn₂ with
  | _ x y =>
    intro h
    apply QuotientGroup.eq.mpr
    have hh : (x.val : G ⧸ Γ) = (y.val : G ⧸ Γ) := h
    have hm : x.val⁻¹ * y.val ∈ Γ := QuotientGroup.eq.mp hh
    exact hm

 omit [TopologicalSpace G] [IsTopologicalGroup G] in
 theorem subgroupLatticeQuotientInclusion_range (Γ H : Subgroup G) :
    range (subgroupLatticeQuotientInclusion Γ H) =
      ((↑) : G → G ⧸ Γ) '' (H : Set G) := by
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    exact ⟨x.val, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(⟨x, hx⟩ : H), rfl⟩

 theorem subgroupLatticeQuotientInclusion_closedEmbedding [T2Space G]
    (Γ H : Subgroup G) [IsClosed (Γ : Set G)] [CompactSpace (H ⧸ Γ.comap H.subtype)] :
    IsClosedEmbedding (subgroupLatticeQuotientInclusion Γ H) := by
  exact (subgroupLatticeQuotientInclusion_continuous Γ H).isClosedEmbedding
    (subgroupLatticeQuotientInclusion_injective Γ H)

 omit [IsTopologicalGroup G] in
 theorem subgroupLatticeOrbit_isCompact (Γ H : Subgroup G)
    [CompactSpace (H ⧸ Γ.comap H.subtype)] :
    IsCompact (((↑) : G → G ⧸ Γ) '' (H : Set G)) := by
  have hc := isCompact_univ.image (subgroupLatticeQuotientInclusion_continuous Γ H)
  simpa only [image_univ, subgroupLatticeQuotientInclusion_range] using hc

end Hindman168
