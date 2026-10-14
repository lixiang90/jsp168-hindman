import Hindman168.EventMass

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem event_le_total_of_pointwise {α : Type*} (μ ν : Mass α) (E : α → Prop)
    (h : ∀ x, (if E x then μ x else 0) ≤ ν x) : event μ E ≤ total ν := by
  rw [event_eq_sum μ E (Finset.subset_union_left (s₂ := ν.support)),
    total_eq_sum ν (Finset.subset_union_right (s₁ := μ.support))]
  exact Finset.sum_le_sum (fun x _ => h x)

theorem event_or_le_add {α : Type*} (μ : Mass α) (E F : α → Prop)
    (hμ : ∀ x, 0 ≤ μ x) : event μ (fun x => E x ∨ F x) ≤ event μ E + event μ F := by
  simp only [event_eq_sum _ _ (Finset.Subset.refl _)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf, hμ x]

end Hindman168.FiniteMass
