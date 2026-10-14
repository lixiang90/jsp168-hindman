import Hindman168.FiniteConditionalLikelihood
import Hindman168.FiniteEventComparison
import Mathlib.Tactic

/-! Exact §8.5 budgets, retaining arbitrary earlier events. The exceptional
conditioning mass is unconditional; no lower bound on the earlier event is used. -/
namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

theorem principal_conditional_lower_with_exception {α β : Type*}
    (μ : Mass α) (ν : α → Mass β) (E G : α → Prop) (P : α → β → Prop)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x y, 0 ≤ ν x y)
    (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hgood : ∀ x ∈ μ.support, G x → c - ε ≤ event (ν x) (P x)) :
    c * event μ E - c * event μ (fun x => ¬ G x) - ε * total μ ≤
      event (conditionalJoint μ ν) (fun xy => E xy.1 ∧ P xy.1 xy.2) := by
  rw [event_conditionalJoint, event_eq_sum μ E (Finset.Subset.refl _),
    event_eq_sum μ (fun x => ¬ G x) (Finset.Subset.refl _),
    total_eq_sum μ (Finset.Subset.refl _), Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro x hx
  change _ ≤ μ x * event (ν x) (fun y => E x ∧ P x y)
  have hp := event_nonneg (ν x) (P x) (hν x)
  by_cases he : E x <;> by_cases hg : G x
  · simp only [he, hg, not_true_eq_false, if_true, if_false, true_and, mul_zero, sub_zero]
    nlinarith [mul_le_mul_of_nonneg_left (hgood x hx hg) (hμ x)]
  · simp only [he, hg, not_false_eq_true, if_true, true_and]
    nlinarith [mul_nonneg (hμ x) hε, mul_nonneg (hμ x) hp]
  · simp only [he, hg, not_true_eq_false, if_false, false_and, event_false, mul_zero]
    nlinarith [mul_nonneg (hμ x) hε]
  · simp only [he, hg, not_false_eq_true, if_true, if_false, false_and, event_false, mul_zero]
    nlinarith [mul_nonneg (hμ x) hε, mul_nonneg (hμ x) hc]

/-- Removing finitely many shifts costs their average L1 error. This works
for arbitrary kernels, including the original signed-integer pivot laws. -/
theorem principal_slot_removal {α β V : Type*} [Fintype V] [Nonempty V]
    (μ : Mass α) (ν : α → Mass β) (ν' : V → α → Mass β)
    (E G : α → Prop) (P : α → β → Prop)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x y, 0 ≤ ν x y)
    (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hgood : ∀ x ∈ μ.support, G x → c ≤ ∑ v, event (ν' v x) (P x))
    (herr : ∀ v x, x ∈ μ.support → distance (ν' v x) (ν x) ≤ ε) :
    (c / Fintype.card V) * event μ E -
      (c / Fintype.card V) * event μ (fun x => ¬ G x) - ε * total μ ≤
      event (conditionalJoint μ ν) (fun xy => E xy.1 ∧ P xy.1 xy.2) := by
  have hv : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  apply principal_conditional_lower_with_exception μ ν E G P hμ hν
    (c / Fintype.card V) ε (div_nonneg hc hv.le) hε
  intro x hx hg
  have hb : ∑ v, event (ν' v x) (P x) ≤
      (Fintype.card V : ℝ) * (event (ν x) (P x) + ε) := by
    calc
      _ ≤ ∑ _v : V, (event (ν x) (P x) + ε) := by
        apply Finset.sum_le_sum
        intro v _
        have hh := (abs_le.mp ((event_difference_le_distance (ν' v x) (ν x) (P x)).trans
          (herr v x hx))).2
        linarith
      _ = _ := by simp; ring
  have hh := (div_le_iff₀ hv).mpr (by nlinarith [hgood x hx hg] : c ≤ (event (ν x) (P x) + ε) * (Fintype.card V : ℝ))
  linarith
end Hindman168
