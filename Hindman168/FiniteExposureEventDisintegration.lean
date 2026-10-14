import Hindman168.FinitePositiveConditioningLimit
import Hindman168.FiniteProductExpectations

namespace Hindman168

open FiniteMass Filter
open scoped BigOperators Topology Classical

theorem finite_exposure_mass_eq_event {α β : Type*} (μ : Mass α) (f : α → β) (y : β) :
    μ.mapDomain f y = event μ (fun x => f x = y) := by
  rw [push_apply, event_eq_sum _ _ (Finset.Subset.refl _)]
  apply Finset.sum_congr rfl
  intro x _
  simp only [eq_comm]

theorem finite_exposure_weighted_event {α β : Type*} (μ : Mass α) (f : α → β)
    (B : α → Prop) (hμ : ∀ x, 0 ≤ μ x) (y : β) :
    μ.mapDomain f y * event (conditionMass μ (fun x => f x = y)) B =
      event μ (fun x => f x = y ∧ B x) := by
  rw [finite_exposure_mass_eq_event, finite_condition_event_inter]
  by_cases he : event μ (fun x => f x = y) = 0
  · have hb := event_mono μ hμ (fun x (h : f x = y ∧ B x) => h.1)
    have hn := event_nonneg μ (fun x => f x = y ∧ B x) hμ
    rw [he] at hb ⊢
    have hz : event μ (fun x => f x = y ∧ B x) = 0 := le_antisymm hb hn
    rw [hz, zero_mul]
  · field_simp

theorem finite_exposure_event_disintegration {α β : Type*} (μ : Mass α) (f : α → β)
    (B : α → Prop) (hμ : ∀ x, 0 ≤ μ x) :
    expectation (μ.mapDomain f) (fun y => event (conditionMass μ (fun x => f x = y)) B) =
      event μ B := by
  rw [expectation_eq_sum _ _ Finsupp.mapDomain_support]
  simp_rw [finite_exposure_weighted_event μ f B hμ,
    event_eq_sum μ (fun x => f x = _ ∧ B x) (Finset.Subset.refl _)]
  rw [Finset.sum_comm, event_eq_sum μ B (Finset.Subset.refl _)]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hb : B x
  · simp [hb, Finset.mem_image_of_mem f hx]
  · simp [hb]

theorem finite_exposure_bad_fiber_bound {α β : Type*} (μ : Mass α) (f : α → β)
    (B : α → Prop) (hμ : ∀ x, 0 ≤ μ x) {ε : ℝ} (hε : 0 < ε) :
    event (μ.mapDomain f) (fun y => ε ≤ event (conditionMass μ (fun x => f x = y)) B) ≤
      event μ B / ε := by
  apply (le_div_iff₀ hε).mpr
  rw [← finite_exposure_event_disintegration μ f B hμ,
    event_eq_sum _ _ (Finset.Subset.refl _), Finset.sum_mul]
  unfold expectation Finsupp.sum
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : ε ≤ event (conditionMass μ (fun x => f x = y)) B
  · rw [if_pos hy]
    exact mul_le_mul_of_nonneg_left hy (push_nonneg μ f hμ y)
  · rw [if_neg hy, zero_mul]
    exact mul_nonneg (push_nonneg μ f hμ y)
      (event_nonneg _ _ (conditionMass_nonneg _ _ hμ))

theorem finite_exposure_bad_fiber_tendsto {α β : Type*}
    (μ : ℕ → Mass α) (f : ℕ → α → β) (B : ℕ → α → Prop)
    (hμ : ∀ᶠ w in atTop, ∀ x, 0 ≤ μ w x)
    (hB : Tendsto (fun w => event (μ w) (B w)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun w => event ((μ w).mapDomain (f w))
      (fun y => ε ≤ event (conditionMass (μ w) (fun x => f w x = y)) (B w))) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (by simpa only [zero_div] using hB.div_const ε)
  · filter_upwards [hμ] with w hw
    exact event_nonneg _ _ (push_nonneg _ _ hw)
  · filter_upwards [hμ] with w hw
    exact finite_exposure_bad_fiber_bound _ _ _ hw hε

end Hindman168
