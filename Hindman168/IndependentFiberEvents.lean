import Hindman168.EventMass

/-!
# Independent event tests after exposing one tuple

All identities retain the original finite weights. A random finite set
of tests may depend on the exposed tuple; a uniform cardinality and a
uniform bound for each independent test suffice to bound their union.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem event_tensor_left {α β : Type*} (μ : Mass α) (ν : Mass β)
    (E : α × β → Prop) :
    event (tensor μ ν) E = ∑ a ∈ μ.support, μ a * event ν (fun b => E (a, b)) := by
  rw [event_eq_sum _ _ (tensor_support μ ν), Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  rw [event_eq_sum ν _ (Finset.Subset.refl _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [tensor_apply]
  split_ifs <;> simp

theorem event_tensor_independent {α β : Type*} (μ : Mass α) (ν : Mass β)
    (E : α → Prop) (F : β → Prop) :
    event (tensor μ ν) (fun x => E x.1 ∧ F x.2) = event μ E * event ν F := by
  rw [event_tensor_left, event_eq_sum μ E (Finset.Subset.refl _), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : E a
  · simp only [ha, true_and, if_true]
  · simp only [ha, false_and, event_false, if_false, mul_zero, zero_mul]

theorem event_tensor_fiber_le {α β : Type*} (μ : Mass α) (ν : Mass β)
    (E : α × β → Prop) (hμ : ∀ a, 0 ≤ μ a) (ht : total μ = 1)
    {B : ℝ} (hB : ∀ a ∈ μ.support, event ν (fun b => E (a, b)) ≤ B) :
    event (tensor μ ν) E ≤ B := by
  rw [event_tensor_left]
  calc
    _ ≤ ∑ a ∈ μ.support, μ a * B :=
      Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hB a ha) (hμ a))
    _ = B := by rw [← Finset.sum_mul, ← total_eq_sum μ (Finset.Subset.refl _), ht, one_mul]

theorem event_tensor_varying_union_le {α β ι : Type*} (μ : Mass α) (ν : Mass β)
    (S : α → Finset ι) (E : α → ι → β → Prop)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b) (ht : total μ = 1)
    {K : ℕ} (hcard : ∀ a ∈ μ.support, (S a).card ≤ K) {b : ℝ} (hb : 0 ≤ b)
    (hcap : ∀ a ∈ μ.support, ∀ i ∈ S a, event ν (E a i) ≤ b) :
    event (tensor μ ν) (fun x => ∃ i ∈ S x.1, E x.1 i x.2) ≤ (K : ℝ) * b := by
  apply event_tensor_fiber_le μ ν _ hμ ht
  intro a ha
  calc
    _ ≤ ∑ i ∈ S a, event ν (E a i) := event_union_bound ν (S a) (E a) hν
    _ ≤ ∑ _i ∈ S a, b := Finset.sum_le_sum (fun i hi => hcap a ha i hi)
    _ = ((S a).card : ℝ) * b := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard a ha) hb

theorem event_tensor_common_test_union_le {α β ι : Type*} (μ : Mass α) (ν : Mass β)
    (S : Finset ι) (E : ι → α → Prop) (F : ι → β → Prop)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b)
    (u v : ι → ℝ) (hu : ∀ i ∈ S, 0 ≤ u i)
    (hE : ∀ i ∈ S, event μ (E i) ≤ u i) (hF : ∀ i ∈ S, event ν (F i) ≤ v i) :
    event (tensor μ ν) (fun x => ∃ i ∈ S, E i x.1 ∧ F i x.2) ≤
      ∑ i ∈ S, u i * v i := by
  apply (event_union_bound _ S (fun i x => E i x.1 ∧ F i x.2)
    (tensor_nonneg μ ν hμ hν)).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [event_tensor_independent]
  exact mul_le_mul (hE i hi) (hF i hi) (event_nonneg ν _ hν) (hu i hi)

theorem event_piMass_main_fiber_le {α : Type*} {n : ℕ} (μ : Fin (n + 1) → Mass α)
    (E : (Fin (n + 1) → α) → Prop) (hμ : ∀ i a, 0 ≤ μ i a)
    (ht : ∀ i, total (μ i) = 1) {b : ℝ}
    (hcap : ∀ x : Fin n → α, event (μ 0) (fun a => E (Fin.cons a x)) ≤ b) :
    event (piMass μ) E ≤ b := by
  rw [event_piMass_cons]
  let ν := piMass (fun i : Fin n => μ i.succ)
  have hν : ∀ x, 0 ≤ ν x := piMass_nonneg _ (fun i => hμ i.succ)
  have htν : total ν = 1 := piMass_total_one _ (fun i => ht i.succ)
  calc
    _ ≤ ∑ x ∈ ν.support, ν x * b :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hcap x) (hν x))
    _ = b := by rw [← Finset.sum_mul, ← total_eq_sum ν (Finset.Subset.refl _), htν, one_mul]

end Hindman168.FiniteMass
