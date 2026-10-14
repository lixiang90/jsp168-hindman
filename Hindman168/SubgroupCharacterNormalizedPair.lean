import Hindman168.SubgroupRealCharacterConjugation
import Hindman168.RoughNormalizedIntegerPair

/-! Exact actual twisted derivative scalar, with genuine subgroup-valued
nonlinear parts and no commutativity assumption on the ambient group. -/
namespace Hindman168
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem subgroup_real_normalized_pair_difference (N : Subgroup G) [N.Normal]
    (hcomm : ∀ x y : G, ⁅x,y⁆ ∈ N) (ψ : N → ℝ)
    (hψ : ∀ x y, ψ (x*y) = ψ x+ψ y)
    (hconj : ∀ g w, ψ (subgroupConjugate N g w) = ψ w)
    (P : ℤ → G) (q : ℤ → N)
    (hq : ∀ m, (q m).val = P m*(P 1^m)⁻¹)
    (t : G) (h n : ℤ) (d : N)
    (hd : d.val = (roughNormalizedIntegerPair P t h n).1 *
      (roughNormalizedIntegerPair P t h n).2⁻¹) :
    ψ d = ψ (q (n+h))-ψ (q n)+(n : ℝ)*ψ (subgroupCommElement N hcomm (P 1) t) := by
  have he : d = subgroupConjugate N t⁻¹ (q (n+h)) *
      subgroupConjugate N t⁻¹ (subgroupCommElement N hcomm (P 1^n) t) * (q n)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul,Subgroup.coe_inv,subgroupConjugate,subgroupCommElement,inv_inv]
    rw [hd,hq,hq,rough_normalized_integer_pair_second]
    simp only [roughNormalizedIntegerPair,commutatorElement_def]
    group
  rw [he,hψ,hψ,hconj,hconj,subgroup_real_character_inv N ψ hψ,
    subgroup_real_commutator_zpow_left N hcomm ψ hψ hconj]
  ring

end Hindman168
