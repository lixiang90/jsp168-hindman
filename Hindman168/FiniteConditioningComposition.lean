import Hindman168.FinitePositiveConditioningLimit

namespace Hindman168.FiniteMass
open scoped BigOperators Classical

theorem conditionMass_twice {α : Type*} (μ : Mass α) (E B : α → Prop)
    (hE : event μ E ≠ 0) :
    conditionMass (conditionMass μ E) B = conditionMass μ (fun x => E x ∧ B x) := by
  ext x
  rw [conditionMass_apply, conditionMass_apply, conditionMass_apply,
    finite_condition_event_inter]
  by_cases he : E x <;> by_cases hb : B x
  · simp only [he, hb, and_self, if_true]
    exact div_div_div_cancel_right₀ hE _ _
  · simp [he, hb]
  · simp [he, hb]
  · simp [he, hb]

theorem conditionMass_piMass {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) (E : ∀ i, α i → Prop) :
    conditionMass (piMass μ) (fun x => ∀ i, E i (x i)) =
      piMass (fun i => conditionMass (μ i) (E i)) := by
  rw [piMass_conditionMass, conditionMass, event_piMass_all]
  rfl

theorem event_conditioned_push {α β : Type*} (μ : Mass α) (p : α → β)
    (E B : β → Prop) :
    event (conditionMass (μ.mapDomain p) E) B =
      event (conditionMass μ (fun x => E (p x))) (fun x => B (p x)) := by
  rw [finite_condition_event_inter, finite_condition_event_inter, event_map, event_map]

theorem conditionMass_all_event_ne_zero {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) (E : ∀ i, α i → Prop)
    (hE : ∀ i, event (μ i) (E i) ≠ 0) :
    event (piMass μ) (fun x => ∀ i, E i (x i)) ≠ 0 := by
  rw [event_piMass_all]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hE i)

end Hindman168.FiniteMass
