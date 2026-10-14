import Hindman168.FiniteConditionalJoint
import Hindman168.FiniteReplicaConditioning

/-!
# Likelihood bounds for the original conditional joint mass

The inner law may depend on the outside variable and need not be normalized.
Conditioning the actual joint mass produces the usual likelihood ratio.
Uniform positive likelihood bounds imply domination of every outside event.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem event_conditionalJoint {α β : Type*} (μ : Mass α) (ν : α → Mass β)
    (E : α × β → Prop) :
    event (conditionalJoint μ ν) E =
      expectation μ (fun x => event (ν x) (fun y => E (x, y))) := by
  rw [event_eq_expectation, expectation_conditionalJoint]
  simp_rw [event_eq_expectation]

theorem event_conditionJoint_outer {α β : Type*} (μ : Mass α) (ν : α → Mass β)
    (E : α × β → Prop) (B : α → Prop) :
    event (conditionMass (conditionalJoint μ ν) E) (fun xy => B xy.1) =
      expectation μ (fun x => if B x then event (ν x) (fun y => E (x, y)) else 0) /
        expectation μ (fun x => event (ν x) (fun y => E (x, y))) := by
  rw [event_eq_expectation, expectation_conditionMass, event_conditionalJoint,
    expectation_conditionalJoint]
  congr 1
  apply congrArg (expectation μ)
  funext x
  by_cases hx : B x
  · simp only [hx, if_true]
    exact (event_eq_expectation _ _).symm
  · simp [hx, expectation]

theorem likelihood_expectation_lower {α : Type*} (μ : Mass α) (L : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (ht : total μ = 1) {b : ℝ}
    (hL : ∀ x ∈ μ.support, b ≤ L x) : b ≤ expectation μ L := by
  calc
    b = ∑ x ∈ μ.support, μ x * b := by
      rw [← Finset.sum_mul, ← total_eq_sum μ (Finset.Subset.refl _), ht, one_mul]
    _ ≤ expectation μ L := Finset.sum_le_sum (fun x hx =>
      mul_le_mul_of_nonneg_left (hL x hx) (hμ x))

theorem likelihood_event_upper {α : Type*} (μ : Mass α) (L : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (B : α → Prop) {b : ℝ}
    (hL : ∀ x ∈ μ.support, L x ≤ b) :
    expectation μ (fun x => if B x then L x else 0) ≤ b * event μ B := by
  rw [event_eq_sum μ B (Finset.Subset.refl _), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hxB : B x
  · simp only [if_pos hxB]
    simpa only [mul_comm b] using mul_le_mul_of_nonneg_left (hL x hx) (hμ x)
  · simp [hxB]

theorem conditionJoint_event_pos {α β : Type*} (μ : Mass α) (ν : α → Mass β)
    (E : α × β → Prop) (hμ : ∀ x, 0 ≤ μ x) (ht : total μ = 1) {b : ℝ}
    (hb : 0 < b) (hlo : ∀ x ∈ μ.support, b ≤ event (ν x) (fun y => E (x, y))) :
    0 < event (conditionalJoint μ ν) E := by
  rw [event_conditionalJoint]
  exact hb.trans_le (likelihood_expectation_lower μ _ hμ ht hlo)

theorem conditionJoint_outer_domination {α β : Type*} (μ : Mass α)
    (ν : α → Mass β) (E : α × β → Prop) (B : α → Prop)
    (hμ : ∀ x, 0 ≤ μ x) (ht : total μ = 1) {b D : ℝ}
    (hb : 0 < b) (hD : 0 ≤ D)
    (hlo : ∀ x ∈ μ.support, b ≤ event (ν x) (fun y => E (x, y)))
    (hhi : ∀ x ∈ μ.support, event (ν x) (fun y => E (x, y)) ≤ D * b) :
    event (conditionMass (conditionalJoint μ ν) E) (fun xy => B xy.1) ≤
      D * event μ B := by
  have hl := likelihood_expectation_lower μ _ hμ ht hlo
  have hu := likelihood_event_upper μ _ hμ B hhi
  rw [event_conditionJoint_outer]
  apply (div_le_iff₀ (hb.trans_le hl)).mpr
  calc
    _ ≤ (D * b) * event μ B := hu
    _ ≤ (D * event μ B) * expectation μ
        (fun x => event (ν x) (fun y => E (x, y))) := by
      nlinarith [mul_le_mul_of_nonneg_left hl (mul_nonneg hD (event_nonneg μ B hμ))]

end Hindman168.FiniteMass
