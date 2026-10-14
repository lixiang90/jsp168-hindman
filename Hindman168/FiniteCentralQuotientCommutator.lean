import Mathlib.GroupTheory.Schreier

/-! A finite actual central quotient implies a finite actual commutator
subgroup. Commutators are unchanged by central right multipliers, so
actual quotient representatives give a finite set of commutator values.
Schur's theorem then applies to this original group. -/

namespace Hindman168
open Set Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_right_central_multiplier_left (a b z : G)
    (hz : z ∈ Subgroup.center G) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  rw [(show Commute z b from (Subgroup.mem_center_iff.mp hz b).symm).commutator_eq]
  simp

theorem commutator_right_central_multiplier_right (a b z : G)
    (hz : z ∈ Subgroup.center G) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  rw [(show Commute a z from Subgroup.mem_center_iff.mp hz a).commutator_eq]
  simp

theorem commutator_eq_of_center_quotient_eq {a a' b b' : G}
    (ha : (QuotientGroup.mk' (Subgroup.center G)) a =
      (QuotientGroup.mk' (Subgroup.center G)) a')
    (hb : (QuotientGroup.mk' (Subgroup.center G)) b =
      (QuotientGroup.mk' (Subgroup.center G)) b') :
    ⁅a, b⁆ = ⁅a', b'⁆ := by
  have hza : a⁻¹ * a' ∈ Subgroup.center G := QuotientGroup.eq.mp ha
  have hzb : b⁻¹ * b' ∈ Subgroup.center G := QuotientGroup.eq.mp hb
  have heA : a * (a⁻¹ * a') = a' := by simp
  have heB : b * (b⁻¹ * b') = b' := by simp
  have hl := commutator_right_central_multiplier_left a b (a⁻¹ * a') hza
  rw [heA] at hl
  have hr := commutator_right_central_multiplier_right a' b (b⁻¹ * b') hzb
  rw [heB] at hr
  exact hl.symm.trans hr.symm

theorem finite_commutator_of_finite_center_quotient
    [Finite (G ⧸ Subgroup.center G)] : Finite (_root_.commutator G) := by
  classical
  let q := QuotientGroup.mk' (Subgroup.center G)
  let f : (G ⧸ Subgroup.center G) × (G ⧸ Subgroup.center G) → G :=
    fun x => ⁅x.1.out, x.2.out⁆
  have hs : commutatorSet G ⊆ Set.range f := by
    rintro x ⟨a, b, rfl⟩
    refine ⟨(q a, q b), ?_⟩
    exact commutator_eq_of_center_quotient_eq (Quotient.out_eq' (q a))
      (Quotient.out_eq' (q b))
  haveI : Finite (commutatorSet G) := (Set.finite_range f).subset hs
  infer_instance

end Hindman168
