import Hindman168.FiniteExposureEventDisintegration
import Hindman168.FiniteWeightedErrors
import Mathlib.Tactic

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical

/-- Integrate a local slot cover using the exact original exposure weights.
Zero-mass fibers need no local assertion and incur no division problem. -/
theorem principal_exposure_slot_cover {α β V : Type*} [Fintype V]
    (ν : Mass α) (f : α → β) (G : β → Prop) (P : V → α → Prop)
    (hν : ∀ x, 0 ≤ ν x) (c : ℝ) (_hc : 0 ≤ c)
    (hlocal : ∀ y ∈ (ν.mapDomain f).support, G y →
      c ≤ ∑ v, event (conditionMass ν (fun x => f x = y)) (P v)) :
    c * (total ν - event ν (fun x => ¬ G (f x))) ≤ ∑ v, event ν (P v) := by
  let ρ := ν.mapDomain f
  have hid : (∑ v, event ν (P v)) =
      ∑ y ∈ ρ.support, ρ y * ∑ v, event (conditionMass ν (fun x => f x = y)) (P v) := by
    simp_rw [← finite_exposure_event_disintegration ν f _ hν]
    unfold expectation Finsupp.sum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    exact (Finset.mul_sum _ _ _).symm
  rw [hid, ← total_push f ν, ← event_map ν f (fun y => ¬ G y)]
  change c * (total ρ - event ρ (fun y => ¬ G y)) ≤ _
  rw [total_eq_sum ρ (Finset.Subset.refl _), event_eq_sum ρ _ (Finset.Subset.refl _),
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hρ : 0 ≤ ρ y := push_nonneg ν f hν y
  by_cases hg : G y
  · simp only [hg, not_true_eq_false, if_false, sub_zero]
    simpa [mul_comm c] using mul_le_mul_of_nonneg_left (hlocal y hy hg) hρ
  · simp only [hg, not_false_eq_true, if_true, sub_self, mul_zero]
    exact mul_nonneg hρ (Finset.sum_nonneg (fun v _ =>
      event_nonneg _ _ (conditionMass_nonneg _ _ hν)))

/-- Markov retains the actual outside mass, without conditioning on an
arbitrary earlier path event or introducing its reciprocal density. -/
theorem principal_outside_markov {α : Type*} (μ : Mass α) (bad : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hbad : ∀ x, 0 ≤ bad x) (a : ℝ) (ha : 0 < a) :
    event μ (fun x => a ≤ bad x) ≤ expectation μ bad / a := by
  apply (le_div_iff₀ ha).mpr
  rw [event_eq_sum μ _ (Finset.Subset.refl _), Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  change (if a ≤ bad x then μ x else 0) * a ≤ μ x * bad x
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h (hμ x)
  · simp only [zero_mul]
    exact mul_nonneg (hμ x) (hbad x)
end Hindman168
