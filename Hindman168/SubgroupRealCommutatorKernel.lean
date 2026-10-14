import Hindman168.SubgroupRealCharacterConjugation

/-! Conjugation invariance forces the commutator pairing to vanish when
the second input belongs to the actual normal subgroup. -/
namespace Hindman168
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem subgroup_real_commutator_normal_right (N : Subgroup G) [N.Normal]
    (hcomm : ∀ x y : G, ⁅x,y⁆ ∈ N) (ψ : N → ℝ)
    (hψ : ∀ x y, ψ (x*y)=ψ x+ψ y)
    (hconj : ∀ g w, ψ (subgroupConjugate N g w)=ψ w) (g : G) (w : N) :
    ψ (subgroupCommElement N hcomm g w.val)=0 := by
  have he : subgroupCommElement N hcomm g w.val = subgroupConjugate N g w*w⁻¹ := by
    apply Subtype.ext
    change ⁅g,w.val⁆ = g*w.val*g⁻¹*w.val⁻¹
    exact commutatorElement_def g w.val
  rw [he,hψ,hconj,subgroup_real_character_inv N ψ hψ,add_neg_cancel]

end Hindman168
