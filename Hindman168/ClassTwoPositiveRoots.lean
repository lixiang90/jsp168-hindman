import Hindman168.CentralRootMultiplication
import Mathlib.GroupTheory.Nilpotent

/-! The class-two base of nonnormal root collection. The actual second
lower-central layer is trivial, so actual commutators are central.
Every specified subgroup, including a nonnormal one, then has a genuine
positive-root subgroup with the explicit two-denominator product power. -/

namespace Hindman168
open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_le_center_of_lowerCentral_two_bot
    (h : (⊤ : Subgroup G).lowerCentralSeries 2 = ⊥) :
    _root_.commutator G ≤ Subgroup.center G :=
  Subgroup.commutator_top_right_eq_bot_iff_le_center.mp h

theorem commutator_le_center_of_nilpotencyClass_le_two [Group.IsNilpotent G]
    (h : Group.nilpotencyClass G ≤ 2) :
    _root_.commutator G ≤ Subgroup.center G :=
  commutator_le_center_of_lowerCentral_two_bot
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr h)

def classTwoPositiveRootSubgroup (Γ : Subgroup G)
    (h : (⊤ : Subgroup G).lowerCentralSeries 2 = ⊥) : Subgroup G where
  carrier := positiveSubgroupRoots Γ
  one_mem' := subgroup_mem_positiveRoots Γ Γ.one_mem
  mul_mem' := by
    intro a b ha hb
    apply positiveSubgroupRoots_mul_of_central_commutator Γ ha hb
    exact commutator_le_center_of_lowerCentral_two_bot h
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  inv_mem' := positiveSubgroupRoots_inv Γ

theorem classTwoPositiveRootSubgroup_mem_iff (Γ : Subgroup G)
    (h : (⊤ : Subgroup G).lowerCentralSeries 2 = ⊥) (g : G) :
    g ∈ classTwoPositiveRootSubgroup Γ h ↔ g ∈ positiveSubgroupRoots Γ := Iff.rfl

end Hindman168
