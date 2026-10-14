import Hindman168.CentralCommutatorPowers

/-! Genuine multiplicativity of a central commutator in each variable.
The homomorphisms use the specified original subgroups as their domains;
no abelian replacement group or additive logarithm is assumed. -/

namespace Hindman168
open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_mul_left_of_central (a b c : G)
    (hbc : ⁅b, c⁆ ∈ Subgroup.center G) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    Subgroup.mem_center_iff.mp hbc a]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  exact (Subgroup.mem_center_iff.mp hbc ⁅a, c⁆).symm

theorem commutator_mul_right_of_central (a b c : G)
    (hac : ⁅a, c⁆ ∈ Subgroup.center G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,
    mul_assoc ⁅a, b⁆ b ⁅a, c⁆, Subgroup.mem_center_iff.mp hac b]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

def centralCommutatorLeftHom (A B : Subgroup G)
    (hc : ⁅A, B⁆ ≤ Subgroup.center G) (b : B) : A →* G where
  toFun a := ⁅(a : G), (b : G)⁆
  map_one' := commutatorElement_one_left _
  map_mul' a a' := commutator_mul_left_of_central (a : G) (a' : G) (b : G)
    (hc (Subgroup.commutator_mem_commutator a'.property b.property))

def centralCommutatorRightHom (A B : Subgroup G)
    (hc : ⁅A, B⁆ ≤ Subgroup.center G) (a : A) : B →* G where
  toFun b := ⁅(a : G), (b : G)⁆
  map_one' := commutatorElement_one_right _
  map_mul' b b' := commutator_mul_right_of_central (a : G) (b : G) (b' : G)
    (hc (Subgroup.commutator_mem_commutator a.property b'.property))

theorem centralCommutatorLeftHom_apply (A B : Subgroup G)
    (hc : ⁅A, B⁆ ≤ Subgroup.center G) (b : B) (a : A) :
    centralCommutatorLeftHom A B hc b a = ⁅(a : G), (b : G)⁆ := rfl

theorem centralCommutatorRightHom_apply (A B : Subgroup G)
    (hc : ⁅A, B⁆ ≤ Subgroup.center G) (a : A) (b : B) :
    centralCommutatorRightHom A B hc a b = ⁅(a : G), (b : G)⁆ := rfl

end Hindman168
