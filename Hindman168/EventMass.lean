import Hindman168.FiniteCoordinates
import Mathlib.Data.Fin.Tuple.Finset

/-!
# Events under actual finite probability laws

An event mass is the sum of the original coefficients on the event. The
pushforward and product formulas retain those coefficients, so subsequent
root-count estimates apply to nonuniform sampling as well.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

noncomputable def event {α : Type*} (μ : Mass α) (E : α → Prop) : ℝ :=
  μ.sum (fun x a => if E x then a else 0)

theorem event_eq_sum {α : Type*} (μ : Mass α) (E : α → Prop)
    {S : Finset α} (hS : μ.support ⊆ S) :
    event μ E = ∑ x ∈ S, if E x then μ x else 0 :=
  Finsupp.sum_of_support_subset μ hS _ (by intros; split_ifs <;> rfl)

theorem event_eq_filter {α : Type*} (μ : Mass α) (E : α → Prop) :
    event μ E = ∑ x ∈ μ.support.filter E, μ x := by
  rw [event_eq_sum μ E (Finset.Subset.refl _), Finset.sum_filter]

theorem event_nonneg {α : Type*} (μ : Mass α) (E : α → Prop)
    (hμ : ∀ x, 0 ≤ μ x) : 0 ≤ event μ E := by
  rw [event_eq_filter]
  exact Finset.sum_nonneg (fun x _ => hμ x)

theorem event_mono {α : Type*} (μ : Mass α) {E F : α → Prop}
    (hμ : ∀ x, 0 ≤ μ x) (hEF : ∀ x, E x → F x) : event μ E ≤ event μ F := by
  rw [event_eq_sum μ E (Finset.Subset.refl _),
    event_eq_sum μ F (Finset.Subset.refl _)]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : E x
  · rw [if_pos he, if_pos (hEF x he)]
  · rw [if_neg he]
    split_ifs
    · exact hμ x
    · exact le_rfl

theorem event_le_total {α : Type*} (μ : Mass α) (E : α → Prop)
    (hμ : ∀ x, 0 ≤ μ x) : event μ E ≤ total μ := by
  rw [event_eq_sum μ E (Finset.Subset.refl _),
    total_eq_sum μ (Finset.Subset.refl _)]
  exact Finset.sum_le_sum (fun x _ => by split_ifs <;> simp [hμ x])

theorem event_false {α : Type*} (μ : Mass α) : event μ (fun _ => False) = 0 := by
  simp [event, Finsupp.sum]

theorem event_map {α β : Type*} (μ : Mass α) (f : α → β) (E : β → Prop) :
    event (μ.mapDomain f) E = event μ (fun x => E (f x)) := by
  exact Finsupp.sum_mapDomain_index (by intros; split_ifs <;> rfl)
    (by intros; split_ifs <;> simp)

theorem event_toPMF {α : Type*} (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x)
    (ht : total μ = 1) (E : α → Prop) :
    ((toPMF μ hμ ht).map (fun x => decide (E x))) true = ENNReal.ofReal (event μ E) := by
  rw [toPMF_map_apply, push_apply]
  congr 1
  rw [event_eq_sum μ E (Finset.Subset.refl _)]
  apply Finset.sum_congr rfl
  intro x _
  simp

theorem event_union_bound {α ι : Type*} (μ : Mass α) (S : Finset ι)
    (E : ι → α → Prop) (hμ : ∀ x, 0 ≤ μ x) :
    event μ (fun x => ∃ i ∈ S, E i x) ≤ ∑ i ∈ S, event μ (E i) := by
  simp only [event_eq_sum _ _ (Finset.Subset.refl _)]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : ∃ i ∈ S, E i x
  · rw [if_pos he]
    obtain ⟨i, hi, hei⟩ := he
    have h := Finset.single_le_sum (f := fun j => if E j x then μ x else 0)
      (fun j _ => by split_ifs <;> simp [hμ x]) hi
    simpa only [if_pos hei] using h
  · rw [if_neg he]
    exact Finset.sum_nonneg (fun j _ => by split_ifs <;> simp [hμ x])

theorem event_tensor {α β : Type*} (μ : Mass α) (ν : Mass β)
    (E : α × β → Prop) :
    event (tensor μ ν) E = ∑ b ∈ ν.support, ν b * event μ (fun a => E (a, b)) := by
  rw [event_eq_sum _ _ (tensor_support μ ν), Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [event_eq_sum μ _ (Finset.Subset.refl _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [tensor_apply]
  split_ifs <;> simp [mul_comm]

theorem piMass_zero_tail {α : Type*} {n : ℕ} (μ : Fin (n + 1) → Mass α) :
    (piMass μ).mapDomain (fun x => (x 0, Fin.tail x)) =
      tensor (μ 0) (piMass (fun i => μ i.succ)) := by
  let E := (Fin.consEquiv (fun _ : Fin (n + 1) => α)).symm
  change (piMass μ).mapDomain E = _
  ext x
  rw [Finsupp.mapDomain_equiv_apply, piMass_apply, tensor_apply, piMass_apply,
    Fin.prod_univ_succ]
  simp [E, Fin.consEquiv]

theorem event_piMass_cons {α : Type*} {n : ℕ} (μ : Fin (n + 1) → Mass α)
    (E : (Fin (n + 1) → α) → Prop) :
    event (piMass μ) E =
      ∑ x ∈ (piMass (fun i => μ i.succ)).support,
        piMass (fun i => μ i.succ) x * event (μ 0) (fun a => E (Fin.cons a x)) := by
  have h := event_map (piMass μ) (fun x => (x 0, Fin.tail x))
    (fun y => E (Fin.cons y.1 y.2))
  rw [piMass_zero_tail, event_tensor] at h
  simpa only [Fin.cons_self_tail] using h.symm

end Hindman168.FiniteMass
