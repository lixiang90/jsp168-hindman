import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Algebra.Group.Subgroup.Basic

/-! The natural product equivalence for genuine coset spaces; neither
lattice subgroup is assumed normal. -/

namespace Hindman168

variable {G H : Type*} [Group G] [Group H] (Γ : Subgroup G) (Λ : Subgroup H)

def productCosetMap : (G × H) ⧸ Γ.prod Λ → (G ⧸ Γ) × (H ⧸ Λ) :=
  Quotient.lift (fun p : G × H => ((p.1 : G ⧸ Γ), (p.2 : H ⧸ Λ))) (by
    intro p q hpq
    have h := QuotientGroup.leftRel_apply.mp hpq
    exact Prod.ext (QuotientGroup.eq.mpr h.1) (QuotientGroup.eq.mpr h.2))

theorem productCosetMap_mk (p : G × H) :
    productCosetMap Γ Λ (p : (G × H) ⧸ Γ.prod Λ) = ((p.1 : G ⧸ Γ), (p.2 : H ⧸ Λ)) := rfl

theorem productCosetMap_bijective : Function.Bijective (productCosetMap Γ Λ) := by
  constructor
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro p q hpq
    apply QuotientGroup.eq.mpr
    exact ⟨QuotientGroup.eq.mp (congrArg Prod.fst hpq), QuotientGroup.eq.mp (congrArg Prod.snd hpq)⟩
  · rintro ⟨a, b⟩
    refine Quotient.inductionOn₂ a b ?_
    intro g h
    exact ⟨((g, h) : (G × H) ⧸ Γ.prod Λ), rfl⟩

noncomputable def productCosetEquiv : (G × H) ⧸ Γ.prod Λ ≃ (G ⧸ Γ) × (H ⧸ Λ) :=
  Equiv.ofBijective (productCosetMap Γ Λ) (productCosetMap_bijective Γ Λ)

variable [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
theorem productCosetMap_continuous : Continuous (productCosetMap Γ Λ) := by
  apply (QuotientGroup.isQuotientMap_mk (Γ.prod Λ)).continuous_iff.mpr
  exact (QuotientGroup.continuous_mk.comp continuous_fst).prodMk
    (QuotientGroup.continuous_mk.comp continuous_snd)

theorem productCosetEquiv_symm_continuous : Continuous (productCosetEquiv Γ Λ).symm := by
  let π : G × H → (G ⧸ Γ) × (H ⧸ Λ) := fun p => ((p.1 : G ⧸ Γ), (p.2 : H ⧸ Λ))
  have hπ : IsOpenQuotientMap π := QuotientGroup.isOpenQuotientMap_mk.prodMap
    QuotientGroup.isOpenQuotientMap_mk
  apply hπ.continuous_comp_iff.mp
  have he : (productCosetEquiv Γ Λ).symm ∘ π =
      (fun p : G × H => (p : (G × H) ⧸ Γ.prod Λ)) := by
    funext p
    exact (productCosetEquiv Γ Λ).symm_apply_apply (p : (G × H) ⧸ Γ.prod Λ)
  rw [he]
  exact QuotientGroup.continuous_mk

noncomputable def productCosetHomeomorph : (G × H) ⧸ Γ.prod Λ ≃ₜ (G ⧸ Γ) × (H ⧸ Λ) where
  toEquiv := productCosetEquiv Γ Λ
  continuous_toFun := productCosetMap_continuous Γ Λ
  continuous_invFun := productCosetEquiv_symm_continuous Γ Λ

end Hindman168
