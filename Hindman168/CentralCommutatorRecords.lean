import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Commutator records on actual subgroup generators detect differences
in the subgroup centralizer. A translate lying in the original center
also bounds each commutator by a record of its translating element. -/

namespace Hindman168
open Set
open scoped commutatorElement

variable {G : Type*} [Group G]

 theorem commutator_eq_of_mul_mem_center {k γ : G}
    (hc : k * γ ∈ Subgroup.center G) (s : G) : ⁅γ, s⁆ = ⁅k⁻¹, s⁆ := by
  have hz : ⁅k * γ, s⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp hc s).symm
  calc
    _ = ⁅k⁻¹ * (k * γ), s⁆ := by rw [inv_mul_cancel_left]
    _ = _ := by rw [commutatorElement_mul_left_eq_conj_mul, hz]; simp

 theorem inv_mul_mem_centralizer_of_commutator_records_eq (Γ : Subgroup G)
    {S : Set G} (hS : Subgroup.closure S = Γ) {γ δ : G}
    (h : ∀ s ∈ S, ⁅γ, s⁆ = ⁅δ, s⁆) : δ⁻¹ * γ ∈ Subgroup.centralizer (Γ : Set G) := by
  have he : EqOn (MulAut.conj γ).toMonoidHom (MulAut.conj δ).toMonoidHom S := by
    intro s hs
    change MulAut.conj γ s = MulAut.conj δ s
    rw [conj_eq_commutatorElement_mul, conj_eq_commutatorElement_mul, h s hs]
  have heΓ := MonoidHom.eqOn_closure he
  rw [hS] at heΓ
  apply Subgroup.mem_centralizer_iff.mpr
  intro s hs
  have hs' := heΓ hs
  change γ * s * γ⁻¹ = δ * s * δ⁻¹ at hs'
  have ht := congrArg (fun x : G => δ⁻¹ * x * γ) hs'
  simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using ht.symm

end Hindman168
