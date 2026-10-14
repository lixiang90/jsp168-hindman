import Hindman168.EventMass

/-!
# Event errors under independent finite probability laws

Indicators are bounded by one, so event probabilities differ by at most
the coefficient L1 distance. For n independent probability coordinates,
the product L1 distance is at most the sum of the n coordinate errors.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem event_eq_expectation {α : Type*} (μ : Mass α) (E : α → Prop) :
    event μ E = expectation μ (fun x => if E x then 1 else 0) := by
  simp only [event, expectation, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem event_difference_le_distance {α : Type*} (μ ν : Mass α) (E : α → Prop) :
    |event μ E - event ν E| ≤ distance μ ν := by
  rw [event_eq_expectation, event_eq_expectation]
  simpa only [one_mul] using expectation_difference_bound μ ν
    (fun x => if E x then 1 else 0) 1 (fun x => by split_ifs <;> norm_num)

theorem piMass_probability_distance_sum {α : Type*} (n : ℕ)
    (μ ν : Fin n → Mass α) (hμ : ∀ i a, 0 ≤ μ i a) (hν : ∀ i a, 0 ≤ ν i a)
    (htμ : ∀ i, total (μ i) = 1) (htν : ∀ i, total (ν i) = 1) :
    distance (piMass μ) (piMass ν) ≤ ∑ i, distance (μ i) (ν i) := by
  induction n with
  | zero =>
    have heq : piMass μ = piMass ν := by ext; simp [piMass_apply]
    simp [heq, distance, variation]
  | succ n ih =>
    have hi : Function.Injective (fun x : Fin (n + 1) → α => (x 0, Fin.tail x)) := by
      intro x y h
      have h0 : x 0 = y 0 := congrArg Prod.fst h
      have ht : Fin.tail x = Fin.tail y := congrArg Prod.snd h
      rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, h0, ht]
    have htailμ : variation (piMass (fun i : Fin n => μ i.succ)) = 1 := by
      rw [variation_eq_total (piMass (fun i : Fin n => μ i.succ))
          (piMass_nonneg _ (fun i : Fin n => hμ i.succ)),
        piMass_total_one _ (fun i : Fin n => htμ i.succ)]
    have hν0 : variation (ν 0) = 1 := by rw [variation_eq_total _ (hν 0), htν]
    rw [← distance_push_injective hi, piMass_zero_tail, piMass_zero_tail]
    calc
      _ ≤ distance (μ 0) (ν 0) +
          distance (piMass (fun i : Fin n => μ i.succ)) (piMass (fun i : Fin n => ν i.succ)) := by
        simpa only [htailμ, hν0, mul_one, one_mul] using tensor_distance (μ 0) (ν 0)
          (piMass (fun i : Fin n => μ i.succ)) (piMass (fun i : Fin n => ν i.succ))
      _ ≤ distance (μ 0) (ν 0) + ∑ i : Fin n, distance (μ i.succ) (ν i.succ) :=
        add_le_add le_rfl (ih _ _ (fun i => hμ i.succ) (fun i => hν i.succ)
          (fun i => htμ i.succ) (fun i => htν i.succ))
      _ = _ := (Fin.sum_univ_succ (fun i : Fin (n + 1) => distance (μ i) (ν i))).symm

theorem piMass_probability_event_difference {α : Type*} (n : ℕ)
    (μ ν : Fin n → Mass α) (hμ : ∀ i a, 0 ≤ μ i a) (hν : ∀ i a, 0 ≤ ν i a)
    (htμ : ∀ i, total (μ i) = 1) (htν : ∀ i, total (ν i) = 1)
    (E : (Fin n → α) → Prop) :
    |event (piMass μ) E - event (piMass ν) E| ≤ ∑ i, distance (μ i) (ν i) :=
  (event_difference_le_distance _ _ E).trans (piMass_probability_distance_sum n μ ν hμ hν htμ htν)

theorem piMass_constant_probability_event_difference {α : Type*} (n : ℕ)
    (μ ν : Mass α) (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ a, 0 ≤ ν a)
    (htμ : total μ = 1) (htν : total ν = 1) (E : (Fin n → α) → Prop) :
    |event (piMass (fun _ : Fin n => μ)) E - event (piMass (fun _ : Fin n => ν)) E| ≤
      (n : ℝ) * distance μ ν := by
  simpa using piMass_probability_event_difference n (fun _ => μ) (fun _ => ν)
    (fun _ => hμ) (fun _ => hν) (fun _ => htμ) (fun _ => htν) E

end Hindman168.FiniteMass
