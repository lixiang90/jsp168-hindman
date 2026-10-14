import Hindman168.ConditionalRoughCoprimality

/-! Conditioning depends only on the event on the support of the original
finite mass. These exact equalities also cover events of mass zero. -/

namespace Hindman168.FiniteMass
open scoped BigOperators Classical

theorem event_congr_on_support {α : Type*} (μ : Mass α) (E F : α → Prop)
    (h : ∀ x ∈ μ.support, E x ↔ F x) : event μ E = event μ F := by
  rw [event_eq_sum μ E (Finset.Subset.refl _), event_eq_sum μ F (Finset.Subset.refl _)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [propext (h x hx)]

theorem conditionMass_congr_on_support {α : Type*} (μ : Mass α) (E F : α → Prop)
    (h : ∀ x ∈ μ.support, E x ↔ F x) : conditionMass μ E = conditionMass μ F := by
  ext x
  rw [conditionMass_apply, conditionMass_apply, event_congr_on_support μ E F h]
  by_cases hx : x ∈ μ.support
  · rw [propext (h x hx)]
  · have hz := Finsupp.notMem_support_iff.mp hx
    rw [hz]
    split_ifs <;> simp

theorem conditionMass_support_restriction {α : Type*} (μ : Mass α) (E : α → Prop) :
    conditionMass μ (fun x => x ∈ μ.support ∧ E x) = conditionMass μ E := by
  exact conditionMass_congr_on_support μ _ E (fun x hx => by simp only [hx, true_and])

end Hindman168.FiniteMass
