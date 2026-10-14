import Hindman168.FiniteConditioningComposition
import Hindman168.FiniteTailPivotSelection

namespace Hindman168.FiniteMass
open scoped BigOperators Classical

theorem conditioned_piMass_tailPivot_event {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → Mass α) (E : ι → α → Prop)
    (hE : ∀ i, 0 < event (μ i) (E i))
    (j : Option κ → ι) (hj : Function.Injective j)
    (F B : (κ → α) × α → Prop) :
    event (conditionMass (piMass μ)
      (fun x => (∀ i, E i (x i)) ∧ F (fun k => x (j (some k)), x (j none))))
      (fun x => B (fun k => x (j (some k)), x (j none))) =
    event (conditionMass (conditionalJoint
      (piMass (fun k => conditionMass (μ (j (some k))) (E (j (some k)))))
      (fun _ => conditionMass (μ (j none)) (E (j none)))) F) B := by
  rw [← conditionMass_twice _ _ _ (conditionMass_all_event_ne_zero μ E (fun i => (hE i).ne')),
    conditionMass_piMass]
  have h := event_conditioned_push (piMass (fun i => conditionMass (μ i) (E i)))
    (fun x => (fun k => x (j (some k)), x (j none))) F B
  rw [piMass_select_tailPivot _ j hj (fun i => conditionMass_total _ _ (hE i))] at h
  exact h.symm

theorem event_pos_of_supported_witness {α : Type*} (μ : Mass α) (E : α → Prop)
    (hμ : ∀ x, 0 ≤ μ x) {x : α} (hx : x ∈ μ.support) (he : E x) : 0 < event μ E := by
  rw [event_eq_filter]
  exact Finset.sum_pos' (fun y _ => hμ y)
    ⟨x, Finset.mem_filter.mpr ⟨hx, he⟩,
      lt_of_le_of_ne (hμ x) (Ne.symm (Finsupp.mem_support_iff.mp hx))⟩

theorem conditionMass_true_of_total_one {α : Type*} (μ : Mass α) (ht : total μ = 1) :
    conditionMass μ (fun _ => True) = μ := by
  ext x
  have he : event μ (fun _ => True) = total μ := by simp [event, total]
  simp only [conditionMass_apply, if_true, he, ht, div_one]

end Hindman168.FiniteMass
