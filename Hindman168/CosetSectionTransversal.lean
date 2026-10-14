import Hindman168.CosetSectionCoordinates

/-! The actual sheet meets a POINTWISE transversal exactly at gamma=1. -/

namespace Hindman168
open Set

theorem coset_section_translate_mem_transversal_iff {G : Type*} [Group G]
    (Γ : Subgroup G) (τ : (G ⧸ Γ) → G) (F : Set G)
    (hinj : F.InjOn ((↑) : G → G ⧸ Γ)) (hτF : ∀ q, τ q ∈ F)
    (q : G ⧸ Γ) (γ : Γ) : τ q*(γ : G) ∈ F ↔ γ=1 := by
  constructor
  · intro hγ
    have hp : (τ q : G ⧸ Γ) = (τ q*(γ : G) : G ⧸ Γ) := by
      apply QuotientGroup.eq.mpr
      simpa only [inv_mul_cancel_left] using γ.property
    have he := hinj (hτF q) hγ hp
    apply Subtype.ext
    apply mul_left_cancel (a := τ q)
    simpa only [Subgroup.coe_one, mul_one] using he.symm
  · rintro rfl
    simpa only [Subgroup.coe_one, mul_one] using hτF q

theorem coset_section_transversal_fiber_iff {G : Type*} [Group G]
    (Γ : Subgroup G) (τ : (G ⧸ Γ) → G) (hτ : ∀ q, (τ q : G ⧸ Γ) = q)
    (F : Set G) (hinj : F.InjOn ((↑) : G → G ⧸ Γ)) (hτF : ∀ q, τ q ∈ F)
    (A : Set (G ⧸ Γ)) (q : G ⧸ Γ) (γ : Γ) :
    τ q*(γ : G) ∈ (((↑) : G → G ⧸ Γ) ⁻¹' A ∩ F) ↔ q ∈ A ∧ γ=1 := by
  have hp : (τ q*(γ : G) : G ⧸ Γ) = q := coset_section_equiv_coset Γ τ hτ (q,γ)
  simp only [Set.mem_inter_iff, Set.mem_preimage, hp,
    coset_section_translate_mem_transversal_iff Γ τ F hinj hτF]

end Hindman168
