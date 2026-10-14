import Hindman168.CentralSubgroupFactorMap

/-! Fibers of the ACTUAL image-lattice central-subgroup factor are EXACT
original N-action orbits. No normality of the original lattice is needed. -/

namespace Hindman168
variable {G : Type*} [Group G] (N Γ : Subgroup G) [N.Normal]

theorem central_subgroup_factor_fiber_iff (hN : N ≤ Subgroup.center G) (q r : G ⧸ Γ) :
    centralSubgroupFactorMap N Γ q = centralSubgroupFactorMap N Γ r ↔
      ∃ z : N, r = (z : G) • q := by
  constructor
  · induction q, r using Quotient.inductionOn₂ with
    | _ g h =>
      intro he
      let f := QuotientGroup.mk' N
      have hm : f (g⁻¹*h) ∈ Γ.map f := by
        simpa only [centralSubgroupFactorMap, subgroupQuotientImageMap_mk,
          map_mul, map_inv] using QuotientGroup.eq.mp he
      obtain ⟨γ,hγ,hπ⟩ := hm
      have hz : g⁻¹*h*γ⁻¹ ∈ N := by
        apply (QuotientGroup.eq_one_iff _).mp
        change f (g⁻¹*h*γ⁻¹) = 1
        rw [map_mul,map_inv,← hπ,mul_inv_cancel]
      let z : N := ⟨g⁻¹*h*γ⁻¹,hz⟩
      have hzg : (z : G)*g = h*γ⁻¹ := by
        rw [← Subgroup.mem_center_iff.mp (hN z.property) g]
        change g*(g⁻¹*h*γ⁻¹) = h*γ⁻¹
        simp only [← mul_assoc,mul_inv_cancel,one_mul]
      refine ⟨z,?_⟩
      change (h : G ⧸ Γ) = ((z : G)*g : G ⧸ Γ)
      apply QuotientGroup.eq.mpr
      rw [hzg]
      simpa only [← mul_assoc,inv_mul_cancel,one_mul] using Γ.inv_mem hγ
  · rintro ⟨z,rfl⟩
    exact (central_subgroup_factor_map_invariant N Γ z q).symm

end Hindman168
