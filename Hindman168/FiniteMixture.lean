import Hindman168.FiniteMass
import Mathlib.Data.Finsupp.SMul

/-!
# Finite mixtures in the sum-of-absolute-masses norm

Comparison components may be unnormalized. Only the mixing coefficients
are required to form a probability vector for a uniform error bound.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators

theorem total_add {α : Type*} (μ ν : Mass α) : total (μ + ν) = total μ + total ν :=
  Finsupp.sum_add_index' (by intros; rfl) (by intros; rfl)

theorem total_smul {α : Type*} (a : ℝ) (μ : Mass α) : total (a • μ) = a * total μ := by
  rw [total_eq_sum _ (Finsupp.support_smul : (a • μ).support ⊆ μ.support)]
  simp only [Finsupp.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rfl

theorem total_finset_sum {α ι : Type*} (S : Finset ι) (μ : ι → Mass α) :
    total (∑ i ∈ S, μ i) = ∑ i ∈ S, total (μ i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [total]
  | @insert i S hi ih => simp only [Finset.sum_insert hi, total_add, ih]

theorem variation_smul {α : Type*} (a : ℝ) (μ : Mass α) :
    variation (a • μ) = |a| * variation μ := by
  rw [variation_eq_sum _ (Finsupp.support_smul : (a • μ).support ⊆ μ.support)]
  simp only [Finsupp.smul_apply, smul_eq_mul, abs_mul, ← Finset.mul_sum]
  rfl

theorem variation_add {α : Type*} (μ ν : Mass α) :
    variation (μ + ν) ≤ variation μ + variation ν := by
  classical
  let S := μ.support ∪ ν.support
  rw [variation_eq_sum _ (show (μ + ν).support ⊆ S from Finsupp.support_add),
    variation_eq_sum μ (show μ.support ⊆ S from Finset.subset_union_left),
    variation_eq_sum ν (show ν.support ⊆ S from Finset.subset_union_right),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun x _ => abs_add_le (μ x) (ν x))

theorem variation_finset_sum {α ι : Type*} (S : Finset ι) (μ : ι → Mass α) :
    variation (∑ i ∈ S, μ i) ≤ ∑ i ∈ S, variation (μ i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [variation]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (variation_add _ _).trans (add_le_add le_rfl ih)

noncomputable def mixture {α ι : Type*} (S : Finset ι) (p : ι → ℝ) (μ : ι → Mass α) : Mass α :=
  ∑ i ∈ S, p i • μ i

theorem mixture_apply {α ι : Type*} (S : Finset ι) (p : ι → ℝ) (μ : ι → Mass α) (x : α) :
    mixture S p μ x = ∑ i ∈ S, p i * μ i x := by
  classical
  simp only [mixture, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem mixture_nonneg {α ι : Type*} {S : Finset ι} {p : ι → ℝ} {μ : ι → Mass α}
    (hp : ∀ i ∈ S, 0 ≤ p i) (hμ : ∀ i ∈ S, ∀ x, 0 ≤ μ i x) (x : α) :
    0 ≤ mixture S p μ x := by
  rw [mixture_apply]
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hp i hi) (hμ i hi x))

theorem mixture_total {α ι : Type*} (S : Finset ι) (p : ι → ℝ) (μ : ι → Mass α) :
    total (mixture S p μ) = ∑ i ∈ S, p i * total (μ i) := by
  rw [mixture, total_finset_sum]
  simp only [total_smul]

/-- Mixing averages errors without assuming comparison components have mass one. -/
theorem mixture_distance_le {α ι : Type*} {S : Finset ι} {p : ι → ℝ}
    (μ ν : ι → Mass α) (hp : ∀ i ∈ S, 0 ≤ p i) :
    distance (mixture S p μ) (mixture S p ν) ≤ ∑ i ∈ S, p i * distance (μ i) (ν i) := by
  classical
  have he : mixture S p μ - mixture S p ν = ∑ i ∈ S, p i • (μ i - ν i) := by
    simp only [mixture, smul_sub, Finset.sum_sub_distrib]
  rw [distance, he]
  calc
    _ ≤ ∑ i ∈ S, variation (p i • (μ i - ν i)) := variation_finset_sum _ _
    _ = ∑ i ∈ S, p i * distance (μ i) (ν i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [variation_smul, abs_of_nonneg (hp i hi)]
      rfl

theorem mixture_distance_uniform {α ι : Type*} {S : Finset ι} {p : ι → ℝ}
    (μ ν : ι → Mass α) (hp : ∀ i ∈ S, 0 ≤ p i) (ht : ∑ i ∈ S, p i = 1)
    {E : ℝ} (he : ∀ i ∈ S, distance (μ i) (ν i) ≤ E) :
    distance (mixture S p μ) (mixture S p ν) ≤ E := by
  calc
    _ ≤ ∑ i ∈ S, p i * distance (μ i) (ν i) := mixture_distance_le μ ν hp
    _ ≤ ∑ i ∈ S, p i * E :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (he i hi) (hp i hi))
    _ = E := by rw [← Finset.sum_mul, ht, one_mul]

theorem mixture_mass_error {α ι : Type*} {S : Finset ι} {p : ι → ℝ}
    (μ : ι → Mass α) (hp : ∀ i ∈ S, 0 ≤ p i) (ht : ∑ i ∈ S, p i = 1)
    {E : ℝ} (he : ∀ i ∈ S, |total (μ i) - 1| ≤ E) :
    |total (mixture S p μ) - 1| ≤ E := by
  rw [mixture_total]
  have hsum : (∑ i ∈ S, p i * total (μ i)) - 1 = ∑ i ∈ S, p i * (total (μ i) - 1) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_one, ht]
  rw [hsum]
  calc
    _ ≤ ∑ i ∈ S, |p i * (total (μ i) - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ S, p i * |total (μ i) - 1| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hp i hi)]
    _ ≤ ∑ i ∈ S, p i * E :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (he i hi) (hp i hi))
    _ = E := by rw [← Finset.sum_mul, ht, one_mul]

/-- Arbitrary finite pushforwards sum the coefficients in each fiber. -/
theorem push_apply {α β : Type*} [DecidableEq β] (μ : Mass α) (f : α → β) (b : β) :
    μ.mapDomain f b = ∑ a ∈ μ.support, if b = f a then μ a else 0 := by
  classical
  simp only [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply,
    eq_comm]

theorem push_nonneg {α β : Type*} (μ : Mass α) (f : α → β) (hμ : ∀ a, 0 ≤ μ a) (b : β) :
    0 ≤ μ.mapDomain f b := by
  classical
  rw [push_apply]
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hμ a
  · exact le_rfl

end Hindman168.FiniteMass
