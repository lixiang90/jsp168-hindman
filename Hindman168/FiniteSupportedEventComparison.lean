import Hindman168.FiniteSupportedConditioning
import Hindman168.PrimeWeightedDiagonal

namespace Hindman168.FiniteMass
open scoped BigOperators Classical

theorem event_mono_on_support {α : Type*} (μ : Mass α) (E B : α → Prop)
    (hμ : ∀ x, 0 ≤ μ x) (h : ∀ x ∈ μ.support, E x → B x) :
    event μ E ≤ event μ B := by
  rw [event_eq_sum μ E (Finset.Subset.refl _), event_eq_sum μ B (Finset.Subset.refl _)]
  apply Finset.sum_le_sum
  intro x hx
  by_cases he : E x
  · rw [if_pos he, if_pos (h x hx he)]
  · rw [if_neg he]
    split_ifs
    · exact hμ x
    · rfl

theorem event_piMass_coordinate {ι α : Type*} [Fintype ι]
    (μ : ι → Mass α) (ht : ∀ i, total (μ i) = 1) (i : ι) (E : α → Prop) :
    event (piMass μ) (fun x => E (x i)) = event (μ i) E := by
  rw [event_eq_expectation, event_eq_expectation]
  convert expectation_piMass_coordinate μ ht i (fun p => if E p then (1 : ℝ) else 0) using 1

end Hindman168.FiniteMass
