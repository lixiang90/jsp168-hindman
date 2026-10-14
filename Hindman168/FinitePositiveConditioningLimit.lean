import Hindman168.FiniteReplicaConditioning
import Mathlib.Topology.Algebra.Order.Field

namespace Hindman168

open FiniteMass Filter
open scoped BigOperators Topology Classical

theorem finite_condition_event_inter {α : Type*} (μ : Mass α) (E B : α → Prop) :
    event (conditionMass μ E) B = event μ (fun x => E x ∧ B x) / event μ E := by
  rw [event_eq_expectation, expectation_conditionMass, event_eq_expectation]
  congr 1
  rw [event_eq_expectation]
  apply congrArg (expectation μ)
  funext x
  split_ifs <;> simp_all

theorem finite_condition_event_lower_bound {α : Type*} (μ : Mass α) (E B : α → Prop)
    (hμ : ∀ x, 0 ≤ μ x) {c : ℝ} (hc : 0 < c) (hE : c ≤ event μ E) :
    event (conditionMass μ E) B ≤ event μ B / c := by
  rw [finite_condition_event_inter]
  have he := hc.trans_le hE
  exact (div_le_div_of_nonneg_right (event_mono μ hμ (fun _ h => h.2)) he.le).trans
    (div_le_div_of_nonneg_left (event_nonneg μ B hμ) hc hE)

theorem finite_positive_conditioning_zero_limit {α : Type*}
    (μ : ℕ → Mass α) (E B : ℕ → α → Prop)
    (hμ : ∀ᶠ w in atTop, ∀ x, 0 ≤ μ w x) {c : ℝ} (hc : 0 < c)
    (hE : ∀ᶠ w in atTop, c ≤ event (μ w) (E w))
    (hB : Tendsto (fun w => event (μ w) (B w)) atTop (𝓝 0)) :
    Tendsto (fun w => event (conditionMass (μ w) (E w)) (B w)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (by simpa only [zero_div] using hB.div_const c)
  · filter_upwards [hμ] with w hw
    exact event_nonneg _ _ (conditionMass_nonneg _ _ hw)
  · filter_upwards [hμ, hE] with w hw he
    exact finite_condition_event_lower_bound _ _ _ hw hc he

end Hindman168
