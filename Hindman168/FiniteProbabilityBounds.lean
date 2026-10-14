import Hindman168.FiniteProductExpectations
import Hindman168.FiniteEventComparison

/-! Exact finite probability bounds for bounded real tests and events. -/

namespace Hindman168.FiniteMass
open scoped Classical

theorem expectation_probability_Icc {α : Type*} (μ : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (ht : total μ = 1) (f : α → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) : expectation μ f ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨expectation_nonneg μ f hμ (fun x => (hf x).1), ?_⟩
  have h := expectation_mono μ f (fun _ => 1) hμ (fun x => (hf x).2)
  have he : expectation μ (fun _ => 1) = 1 := by
    simpa only [expectation, total, mul_one] using ht
  exact h.trans_eq he

theorem event_probability_Icc {α : Type*} (μ : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (ht : total μ = 1) (E : α → Prop) :
    event μ E ∈ Set.Icc (0 : ℝ) 1 := by
  rw [event_eq_expectation]
  exact expectation_probability_Icc μ hμ ht _ (fun _ => by split_ifs <;> norm_num)

end Hindman168.FiniteMass
