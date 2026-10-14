import Hindman168.CentralFactorCosetMap

/-! Factor fibers are EXACTLY original central-action orbits; no normality
of the original lattice is used. -/

namespace Hindman168

variable {G : Type*} [Group G]

theorem central_factor_coset_map_fiber_iff (Γ : Subgroup G) (q r : G ⧸ Γ) :
    centralFactorCosetMap Γ q = centralFactorCosetMap Γ r ↔
      ∃ z : Subgroup.center G, r = (z : G) • q := by
  constructor
  · induction q, r using Quotient.inductionOn₂ with
    | _ g h =>
      intro he
      let f := QuotientGroup.mk' (Subgroup.center G)
      have hm : f (g⁻¹*h) ∈ Γ.map f := by
        simpa only [centralFactorCosetMap, subgroupQuotientImageMap_mk,
          map_mul, map_inv] using QuotientGroup.eq.mp he
      obtain ⟨γ, hγ, hπ⟩ := hm
      have hz : g⁻¹*h*γ⁻¹ ∈ Subgroup.center G := by
        apply (QuotientGroup.eq_one_iff _).mp
        change f (g⁻¹*h*γ⁻¹) = 1
        rw [map_mul, map_inv, ← hπ, mul_inv_cancel]
      let z : Subgroup.center G := ⟨g⁻¹*h*γ⁻¹, hz⟩
      have hzg : (z : G)*g = h*γ⁻¹ := by
        rw [← Subgroup.mem_center_iff.mp z.property g]
        change g*(g⁻¹*h*γ⁻¹) = h*γ⁻¹
        simp only [← mul_assoc, mul_inv_cancel, one_mul]
      refine ⟨z, ?_⟩
      change (h : G ⧸ Γ) = ((z : G)*g : G ⧸ Γ)
      apply QuotientGroup.eq.mpr
      rw [hzg]
      simpa only [← mul_assoc, inv_mul_cancel, one_mul] using Γ.inv_mem hγ
  · rintro ⟨z, rfl⟩
    exact (central_factor_coset_map_central Γ z q).symm

end Hindman168
