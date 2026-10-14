import Hindman168.PredictionOrderedRecurrence
import Hindman168.PredictionMajorantCancellation

/-!
# Event-restricted original law and exact outside-event completion

The original event mass is kept, without division or conditioning to mass
one. Direction laws need normalization only on the retained event. Outside
that event an explicit unit point mass completes the law; exact Fubini
proves that this completion changes no retained average.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

noncomputable def restrictedMass {α : Type*} (μ : Mass α) (E : α → Prop) : Mass α :=
  Finsupp.filter E μ

theorem restrictedMass_apply {α : Type*} (μ : Mass α) (E : α → Prop) (x : α) :
    restrictedMass μ E x = if E x then μ x else 0 := rfl

theorem restrictedMass_nonneg {α : Type*} (μ : Mass α) (E : α → Prop)
    (hμ : ∀ x, 0 ≤ μ x) (x : α) : 0 ≤ restrictedMass μ E x := by
  rw [restrictedMass_apply]
  split_ifs
  · exact hμ x
  · exact le_rfl

theorem mem_restrictedMass_support {α : Type*} (μ : Mass α) (E : α → Prop) (x : α) :
    x ∈ (restrictedMass μ E).support ↔ x ∈ μ.support ∧ E x := by
  simp only [restrictedMass, Finsupp.support_filter, Finset.mem_filter]

theorem expectation_restrictedMass {α : Type*} (μ : Mass α) (E : α → Prop) (f : α → ℝ) :
    expectation (restrictedMass μ E) f = expectation μ (fun x => if E x then f x else 0) := by
  unfold expectation restrictedMass
  rw [Finsupp.sum_filter_index]
  simp only [Finsupp.support_filter, Finsupp.sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

noncomputable def eventCompletedDirectionMass {α : Type*} {h : ℕ}
    (E : α → Prop) (ν : α → Fin h → Mass ℤ) (x : α) (i : Fin h) : Mass ℤ :=
  if E x then ν x i else Finsupp.single 0 1

theorem eventCompletedDirectionMass_nonneg {α : Type*} {h : ℕ}
    (E : α → Prop) (ν : α → Fin h → Mass ℤ)
    (hν : ∀ x, E x → ∀ i t, 0 ≤ ν x i t) (x : α) (i : Fin h) (t : ℤ) :
    0 ≤ eventCompletedDirectionMass E ν x i t := by
  unfold eventCompletedDirectionMass
  split_ifs with hx
  · exact hν x hx i t
  · simp only [Finsupp.single_apply]
    split_ifs <;> norm_num

theorem eventCompletedDirectionMass_total {α : Type*} {h : ℕ}
    (E : α → Prop) (ν : α → Fin h → Mass ℤ)
    (ht : ∀ x, E x → ∀ i, total (ν x i) = 1) (x : α) (i : Fin h) :
    total (eventCompletedDirectionMass E ν x i) = 1 := by
  unfold eventCompletedDirectionMass
  split_ifs with hx
  · exact ht x hx i
  · simp [total]

theorem event_joint_pair_expectation {α β : Type*} {h : ℕ}
    (μ : Mass α) (base : α → Mass β) (E : α → Prop) (ν : α → Fin h → Mass ℤ)
    (f : α → β → (Fin h → ℤ × ℤ) → ℝ) :
    expectation (conditionalJoint (restrictedMass μ E) base)
      (fun p => expectation (piMass (fun i => tensor (eventCompletedDirectionMass E ν p.1 i)
        (eventCompletedDirectionMass E ν p.1 i))) (f p.1 p.2)) =
      Hindman168.conditionalFiniteAverage μ base E (fun x z =>
        expectation (piMass (fun i => tensor (ν x i) (ν x i))) (f x z)) := by
  rw [expectation_conditionalJoint, expectation_restrictedMass]
  unfold Hindman168.conditionalFiniteAverage
  congr 1
  funext x
  by_cases hx : E x
  · simp only [hx, ite_true, eventCompletedDirectionMass]
  · simp only [hx, ite_false]

end Hindman168.FiniteMass
