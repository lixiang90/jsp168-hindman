import Hindman168.FiniteMixture
import Hindman168.EventMass

/-!
# Exact event averaging over independent finite mixtures

These identities keep the original component weights. A common component
event bound survives averaging whenever each mixing vector has total one.
The coordinate-mixture formula supplies the actual independently sampled
tuple law; independent component choices are not an added assumption.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem event_add {α : Type*} (μ ν : Mass α) (E : α → Prop) :
    event (μ + ν) E = event μ E + event ν E := by
  unfold event
  exact Finsupp.sum_add_index' (by intros; split_ifs <;> rfl)
    (by intros; split_ifs <;> simp)

theorem event_smul {α : Type*} (c : ℝ) (μ : Mass α) (E : α → Prop) :
    event (c • μ) E = c * event μ E := by
  rw [event_eq_sum _ E (Finsupp.support_smul : (c • μ).support ⊆ μ.support),
    event_eq_sum μ E (Finset.Subset.refl _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finsupp.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem event_finset_sum {α ι : Type*} (S : Finset ι) (μ : ι → Mass α) (E : α → Prop) :
    event (∑ i ∈ S, μ i) E = ∑ i ∈ S, event (μ i) E := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [event, Finsupp.sum]
  | @insert i S hi ih => simp only [Finset.sum_insert hi, event_add, ih]

theorem event_mixture {α ι : Type*} (S : Finset ι) (p : ι → ℝ)
    (μ : ι → Mass α) (E : α → Prop) :
    event (mixture S p μ) E = ∑ i ∈ S, p i * event (μ i) E := by
  rw [mixture, event_finset_sum]
  simp only [event_smul]

theorem tensor_mixtures {α β ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (p : ι → ℝ) (q : κ → ℝ) (μ : ι → Mass α) (ν : κ → Mass β) :
    tensor (mixture S p μ) (mixture T q ν) =
      mixture (S.product T) (fun ij => p ij.1 * q ij.2) (fun ij => tensor (μ ij.1) (ν ij.2)) := by
  classical
  ext xy
  simp only [tensor_apply, mixture_apply, Finset.product_eq_sprod, Finset.sum_product]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem event_tensor_mixtures_uniform_le {α β ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (p : ι → ℝ) (q : κ → ℝ) (μ : ι → Mass α) (ν : κ → Mass β)
    (E : α × β → Prop) (hp : ∀ i ∈ S, 0 ≤ p i) (hq : ∀ j ∈ T, 0 ≤ q j)
    (htp : ∑ i ∈ S, p i = 1) (htq : ∑ j ∈ T, q j = 1)
    {B : ℝ} (hB : ∀ i ∈ S, ∀ j ∈ T, event (tensor (μ i) (ν j)) E ≤ B) :
    event (tensor (mixture S p μ) (mixture T q ν)) E ≤ B := by
  rw [tensor_mixtures, event_mixture]
  have ht : ∑ ij ∈ S.product T, p ij.1 * q ij.2 = 1 := by
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp only [← Finset.mul_sum, htq, mul_one, htp]
  calc
    _ ≤ ∑ ij ∈ S.product T, (p ij.1 * q ij.2) * B := by
      apply Finset.sum_le_sum
      intro ij hij
      obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
      exact mul_le_mul_of_nonneg_left (hB ij.1 hi ij.2 hj) (mul_nonneg (hp _ hi) (hq _ hj))
    _ = B := by rw [← Finset.sum_mul, ht, one_mul]

theorem piMass_mixtures {ι κ α : Type*} [Fintype ι] [hι : DecidableEq ι]
    (S : ι → Finset κ) (p : ι → κ → ℝ) (μ : ι → κ → Mass α) :
    piMass (fun i => mixture (S i) (p i) (μ i)) =
      mixture (Fintype.piFinset S) (fun e => ∏ i, p i (e i))
        (fun e => piMass (fun i => μ i (e i))) := by
  classical
  letI : DecidableEq ι := hι
  ext x
  simp only [piMass_apply, mixture_apply]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact Finset.prod_mul_distrib

end Hindman168.FiniteMass
