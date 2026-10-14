import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith

/-! Exact real characters of normal subgroups and their commutator pairing.
All algebraic hypotheses are explicit and are discharged by the native
relative-group application. -/
namespace Hindman168
open scoped commutatorElement
variable {G : Type*} [Group G]

def subgroupConjugate (N : Subgroup G) [N.Normal] (g : G) (w : N) : N :=
  ⟨g*w.val*g⁻¹,(inferInstance : N.Normal).conj_mem w.val w.property g⟩

theorem subgroup_real_character_one (N : Subgroup G) (ψ : N → ℝ)
    (hψ : ∀ x y, ψ (x*y) = ψ x+ψ y) : ψ 1 = 0 := by
  have h := hψ 1 1
  rw [one_mul] at h
  linarith

theorem subgroup_real_character_inv (N : Subgroup G) (ψ : N → ℝ)
    (hψ : ∀ x y, ψ (x*y) = ψ x+ψ y) (w : N) : ψ w⁻¹ = -ψ w := by
  have h := hψ w w⁻¹
  rw [mul_inv_cancel,subgroup_real_character_one N ψ hψ] at h
  linarith

def subgroupCommElement (N : Subgroup G) (hcomm : ∀ x y : G, ⁅x,y⁆ ∈ N)
    (x y : G) : N := ⟨⁅x,y⁆,hcomm x y⟩

theorem subgroup_real_commutator_mul_left (N : Subgroup G) [N.Normal]
    (hcomm : ∀ x y : G, ⁅x,y⁆ ∈ N) (ψ : N → ℝ)
    (hψ : ∀ x y, ψ (x*y) = ψ x+ψ y)
    (hconj : ∀ g w, ψ (subgroupConjugate N g w) = ψ w) (x y z : G) :
    ψ (subgroupCommElement N hcomm (x*y) z) =
      ψ (subgroupCommElement N hcomm x z)+ψ (subgroupCommElement N hcomm y z) := by
  have he : subgroupCommElement N hcomm (x*y) z =
      subgroupConjugate N x (subgroupCommElement N hcomm y z)*subgroupCommElement N hcomm x z := by
    apply Subtype.ext
    change ⁅x*y,z⁆ = (x*⁅y,z⁆*x⁻¹)*⁅x,z⁆
    simp only [commutatorElement_def]
    group
  rw [he,hψ,hconj,add_comm]

theorem subgroup_real_commutator_mul_right (N : Subgroup G) [N.Normal]
    (hcomm : ∀ x y : G, ⁅x,y⁆ ∈ N) (ψ : N → ℝ)
    (hψ : ∀ x y, ψ (x*y) = ψ x+ψ y)
    (hconj : ∀ g w, ψ (subgroupConjugate N g w) = ψ w) (x y z : G) :
    ψ (subgroupCommElement N hcomm x (y*z)) =
      ψ (subgroupCommElement N hcomm x y)+ψ (subgroupCommElement N hcomm x z) := by
  have he : subgroupCommElement N hcomm x (y*z) =
      subgroupCommElement N hcomm x y*subgroupConjugate N y (subgroupCommElement N hcomm x z) := by
    apply Subtype.ext
    change ⁅x,y*z⁆ = ⁅x,y⁆*(y*⁅x,z⁆*y⁻¹)
    simp only [commutatorElement_def]
    group
  rw [he,hψ,hconj]

theorem subgroup_real_commutator_zpow_left (N : Subgroup G) [N.Normal]
    (hcomm : ∀ x y : G, ⁅x,y⁆ ∈ N) (ψ : N → ℝ)
    (hψ : ∀ x y, ψ (x*y) = ψ x+ψ y)
    (hconj : ∀ g w, ψ (subgroupConjugate N g w) = ψ w) (x y : G) (n : ℤ) :
    ψ (subgroupCommElement N hcomm (x^n) y) = (n : ℝ)*ψ (subgroupCommElement N hcomm x y) := by
  let φ : G →* Multiplicative ℝ := {
    toFun := fun z => Multiplicative.ofAdd (ψ (subgroupCommElement N hcomm z y))
    map_one' := by
      change ψ (subgroupCommElement N hcomm 1 y) = 0
      have he : subgroupCommElement N hcomm 1 y = 1 := by
        apply Subtype.ext
        change ⁅(1 : G),y⁆ = 1
        simp
      rw [he,subgroup_real_character_one N ψ hψ]
    map_mul' := fun a b => subgroup_real_commutator_mul_left N hcomm ψ hψ hconj a b y }
  have he := φ.map_zpow x n
  change ψ (subgroupCommElement N hcomm (x^n) y) =
    n • ψ (subgroupCommElement N hcomm x y) at he
  simpa only [zsmul_eq_mul] using he

theorem subgroup_real_twisted_zpow (N : Subgroup G) [N.Normal]
    (hcomm : ∀ x y : G, ⁅x,y⁆ ∈ N) (ψ : N → ℝ)
    (hψ : ∀ x y, ψ (x*y) = ψ x+ψ y)
    (hconj : ∀ g w, ψ (subgroupConjugate N g w) = ψ w) (a t : G) (n : ℤ) :
    ψ (subgroupConjugate N t⁻¹ (subgroupCommElement N hcomm (a^n) t)) =
      (n : ℝ)*ψ (subgroupCommElement N hcomm a t) := by
  rw [hconj]
  exact subgroup_real_commutator_zpow_left N hcomm ψ hψ hconj a t n

end Hindman168
