import Mathlib.MeasureTheory.Measure.Haar.Quotient

/-! An actual section gives an exact measurable group decomposition into
original cosets times ORIGINAL lattice elements, without normality. -/

namespace Hindman168

variable {G : Type*} [Group G]

noncomputable def cosetSectionEquiv (Γ : Subgroup G) (τ : (G ⧸ Γ) → G)
    (hτ : ∀ q, (τ q : G ⧸ Γ) = q) : ((G ⧸ Γ) × Γ) ≃ G where
  toFun p := τ p.1 * p.2
  invFun g := ((g : G ⧸ Γ), ⟨(τ (g : G ⧸ Γ))⁻¹*g, QuotientGroup.eq.mp (hτ (g : G ⧸ Γ))⟩)
  left_inv p := by
    have hq : (τ p.1*(p.2 : G) : G ⧸ Γ) = p.1 := by
      calc
        _ = (τ p.1 : G ⧸ Γ) := by
          symm
          apply QuotientGroup.eq.mpr
          simpa only [inv_mul_cancel_left] using p.2.property
        _ = _ := hτ p.1
    apply Prod.ext
    · exact hq
    · apply Subtype.ext
      change (τ (τ p.1*(p.2 : G) : G ⧸ Γ))⁻¹*(τ p.1*(p.2 : G)) = (p.2 : G)
      rw [hq, inv_mul_cancel_left]
  right_inv g := mul_inv_cancel_left _ _

noncomputable def cosetSectionMeasurableEquiv [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (Γ : Subgroup G) (τ : (G ⧸ Γ) → G) (hτ : ∀ q, (τ q : G ⧸ Γ) = q)
    (hmτ : Measurable τ) : ((G ⧸ Γ) × Γ) ≃ᵐ G :=
  { cosetSectionEquiv Γ τ hτ with
    measurable_toFun := (hmτ.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
    measurable_invFun := QuotientGroup.measurable_coe.prodMk
      (((hmτ.comp QuotientGroup.measurable_coe).inv.mul measurable_id).subtype_mk) }

theorem coset_section_equiv_apply (Γ : Subgroup G) (τ : (G ⧸ Γ) → G)
    (hτ : ∀ q, (τ q : G ⧸ Γ) = q) (q : G ⧸ Γ) (γ : Γ) :
    cosetSectionEquiv Γ τ hτ (q,γ) = τ q*(γ : G) := rfl

theorem coset_section_equiv_coset (Γ : Subgroup G) (τ : (G ⧸ Γ) → G)
    (hτ : ∀ q, (τ q : G ⧸ Γ) = q) (p : (G ⧸ Γ) × Γ) :
    (cosetSectionEquiv Γ τ hτ p : G ⧸ Γ) = p.1 := by
  have h := congrArg Prod.fst ((cosetSectionEquiv Γ τ hτ).symm_apply_apply p)
  exact h

end Hindman168
