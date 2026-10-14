import Hindman168.FiniteConditionalJoint
import Hindman168.DivisorMaskExpansion

/-!
# Exact independent-replica conditional law

A replica joins its original prime law to its prime-dependent shift law.
Reordering the independent product of these joined samples gives the
original independent prime tuple followed by its exact conditional shift
product. All coefficients are retained, including signed masses.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem conditionalJoint_apply {α β : Type*} (μ : Mass α) (ν : α → Mass β) (p : α × β) :
    conditionalJoint μ ν p = μ p.1 * ν p.1 p.2 := by
  have hp (x : α) : ((ν x).mapDomain (fun y => (x, y))) p =
      if x = p.1 then ν x p.2 else 0 := by
    by_cases hx : x = p.1
    · subst x
      rw [if_pos rfl]
      exact Finsupp.mapDomain_apply (fun _ _ h => (Prod.mk.inj h).2) (ν p.1) p.2
    · rw [if_neg hx, push_apply]
      apply Finset.sum_eq_zero
      intro y _
      exact if_neg (fun h => hx (congrArg Prod.fst h).symm)
  rw [conditionalJoint, mixture_apply]
  simp_rw [hp, mul_ite, mul_zero]
  by_cases hm : p.1 ∈ μ.support
  · simp only [Finset.sum_ite_eq', if_pos hm]
  · simp only [Finset.sum_ite_eq', if_neg hm, Finsupp.notMem_support_iff.mp hm, zero_mul]

noncomputable def replicaPairEquiv {ι : Type*} (α β : ι → Type*) :
    (∀ i, α i × β i) ≃ ((∀ i, α i) × (∀ i, β i)) where
  toFun z := (fun i => (z i).1, fun i => (z i).2)
  invFun xy i := (xy.1 i, xy.2 i)
  left_inv z := by funext i; exact Prod.eta (z i)
  right_inv xy := by cases xy; rfl

theorem piMass_conditionalJoint {ι : Type*} [Fintype ι] {α β : ι → Type*}
    (μ : ∀ i, Mass (α i)) (ν : ∀ i, α i → Mass (β i)) :
    (piMass (fun i => conditionalJoint (μ i) (ν i))).mapDomain (replicaPairEquiv α β) =
      conditionalJoint (piMass μ) (fun x => piMass (fun i => ν i (x i))) := by
  ext p
  rw [Finsupp.mapDomain_equiv_apply]
  simp only [piMass_apply, conditionalJoint_apply, replicaPairEquiv]
  exact Finset.prod_mul_distrib

theorem expectation_piMass_conditionalJoint {ι : Type*} [Fintype ι] {α β : ι → Type*}
    (μ : ∀ i, Mass (α i)) (ν : ∀ i, α i → Mass (β i))
    (f : (∀ i, α i) → (∀ i, β i) → ℝ) :
    expectation (piMass (fun i => conditionalJoint (μ i) (ν i)))
      (fun z => f (fun i => (z i).1) (fun i => (z i).2)) =
      expectation (piMass μ) (fun x => expectation (piMass (fun i => ν i (x i))) (f x)) := by
  have h := congrArg (fun ρ => expectation ρ (fun p => f p.1 p.2)) (piMass_conditionalJoint μ ν)
  rw [expectation_push, expectation_conditionalJoint] at h
  exact h

theorem independent_replicas_product {ι : Type*} [Fintype ι] {α β : ι → Type*}
    (μ : ∀ i, Mass (α i)) (ν : ∀ i, α i → Mass (β i))
    (f : ∀ i, α i → β i → ℝ) :
    (∏ i, expectation (μ i) (fun x => expectation (ν i x) (f i x))) =
      expectation (piMass μ) (fun x => expectation (piMass (fun i => ν i (x i)))
        (fun y => ∏ i, f i (x i) (y i))) := by
  have h := expectation_piMass_product (fun i => conditionalJoint (μ i) (ν i))
    (fun i p => f i p.1 p.2)
  simp only [expectation_conditionalJoint] at h
  exact h.symm.trans (expectation_piMass_conditionalJoint μ ν (fun x y => ∏ i, f i (x i) (y i)))

theorem independent_replicas_root_product {ι γ : Type*} [Fintype ι] {α β : ι → Type*}
    (ρ : Mass γ) (μ : ∀ i, Mass (α i)) (ν : ∀ i, α i → Mass (β i))
    (H : γ → ℝ) (f : ∀ i, α i → β i → γ → ℝ) :
    expectation ρ (fun z => H z * ∏ i, expectation (μ i)
      (fun x => expectation (ν i x) (fun y => f i x y z))) =
      expectation (piMass μ) (fun x => expectation (piMass (fun i => ν i (x i)))
        (fun y => expectation ρ (fun z => H z * ∏ i, f i (x i) (y i) z))) := by
  calc
    _ = expectation ρ (fun z => expectation (piMass μ) (fun x =>
        expectation (piMass (fun i => ν i (x i))) (fun y => H z * ∏ i, f i (x i) (y i) z))) := by
      apply congrArg (expectation ρ)
      funext z
      rw [independent_replicas_product, ← expectation_const_mul]
      apply congrArg (expectation (piMass μ))
      funext x
      rw [expectation_const_mul]
    _ = _ := by
      rw [expectation_comm]
      apply congrArg (expectation (piMass μ))
      funext x
      exact expectation_comm ρ (piMass (fun i => ν i (x i))) _

end Hindman168.FiniteMass
