import Mathlib.Topology.Algebra.Group.Quotient

/-! Natural coset quotient maps induced by an actual continuous group
homomorphism. The specified subgroup need not be normal: these are the
original coset spaces, not replacement group quotients. -/

namespace Hindman168
open Function

variable {G K : Type*} [Group G] [Group K]

def subgroupQuotientImageMap (f : G →* K) (Γ : Subgroup G) :
    G ⧸ Γ → K ⧸ Γ.map f :=
  Quotient.lift (fun g : G => (QuotientGroup.mk (f g) : K ⧸ Γ.map f)) (by
    intro a b h
    apply QuotientGroup.eq.mpr
    rw [← map_inv, ← map_mul]
    exact ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp h, rfl⟩)

theorem subgroupQuotientImageMap_mk (f : G →* K) (Γ : Subgroup G) (g : G) :
    subgroupQuotientImageMap f Γ (QuotientGroup.mk g) = QuotientGroup.mk (f g) := rfl

theorem subgroupQuotientImageMap_surjective (f : G →* K) (Γ : Subgroup G)
    (hf : Surjective f) : Surjective (subgroupQuotientImageMap f Γ) := by
  intro y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective (s := Γ.map f) y
  obtain ⟨g, rfl⟩ := hf k
  exact ⟨QuotientGroup.mk g, rfl⟩

variable [TopologicalSpace G] [TopologicalSpace K]

theorem subgroupQuotientImageMap_continuous (f : G →* K) (Γ : Subgroup G)
    (hf : Continuous f) : Continuous (subgroupQuotientImageMap f Γ) := by
  apply (QuotientGroup.isQuotientMap_mk Γ).continuous_iff.mpr
  exact QuotientGroup.continuous_mk.comp hf

theorem subgroupQuotientImageMap_compactSpace (f : G →* K) (Γ : Subgroup G)
    [CompactSpace (G ⧸ Γ)] (hc : Continuous f) (hs : Surjective f) :
    CompactSpace (K ⧸ Γ.map f) := by
  have h := isCompact_range (subgroupQuotientImageMap_continuous f Γ hc)
  rw [Set.range_eq_univ.mpr (subgroupQuotientImageMap_surjective f Γ hs)] at h
  exact isCompact_univ_iff.mp h

end Hindman168
