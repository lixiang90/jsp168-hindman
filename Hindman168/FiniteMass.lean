import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Finite signed masses and the paper's total-mass norm

All sampling laws used in the paper have finite support at fixed cutoffs.
`variation` is the sum of absolute coefficients (twice probability total
variation for two probability laws). It is not the sup norm on `Finsupp`.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators

abbrev Mass (α : Type*) := α →₀ ℝ

noncomputable def total {α : Type*} (μ : Mass α) : ℝ := μ.sum (fun _ a => a)

noncomputable def variation {α : Type*} (μ : Mass α) : ℝ := μ.sum (fun _ a => |a|)

noncomputable def expectation {α : Type*} (μ : Mass α) (f : α → ℝ) : ℝ :=
  μ.sum (fun x a => a * f x)

noncomputable def distance {α : Type*} (μ ν : Mass α) : ℝ := variation (μ - ν)

theorem total_eq_sum {α : Type*} (μ : Mass α) {S : Finset α} (hS : μ.support ⊆ S) :
    total μ = ∑ x ∈ S, μ x :=
  Finsupp.sum_of_support_subset μ hS _ (by intros; rfl)

theorem variation_eq_sum {α : Type*} (μ : Mass α) {S : Finset α} (hS : μ.support ⊆ S) :
    variation μ = ∑ x ∈ S, |μ x| :=
  Finsupp.sum_of_support_subset μ hS _ (by intros; exact abs_zero)

theorem variation_nonneg {α : Type*} (μ : Mass α) : 0 ≤ variation μ :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem total_sub {α : Type*} (μ ν : Mass α) : total (μ - ν) = total μ - total ν :=
  Finsupp.sum_sub_index (by intros; rfl)

theorem total_push {α β : Type*} (f : α → β) (μ : Mass α) :
    total (μ.mapDomain f) = total μ :=
  Finsupp.sum_mapDomain_index (by intros; rfl) (by intros; rfl)

theorem variation_push_injective {α β : Type*} {f : α → β} (hf : Function.Injective f)
    (μ : Mass α) : variation (μ.mapDomain f) = variation μ := by
  let e : α ↪ β := ⟨f, hf⟩
  have he : μ.mapDomain f = μ.embDomain e := (Finsupp.embDomain_eq_mapDomain e μ).symm
  rw [variation, he, Finsupp.sum_embDomain]
  rfl

theorem distance_push_injective {α β : Type*} {f : α → β} (hf : Function.Injective f)
    (μ ν : Mass α) : distance (μ.mapDomain f) (ν.mapDomain f) = distance μ ν := by
  rw [distance, ← Finsupp.mapDomain_sub, variation_push_injective hf]
  rfl

theorem variation_eq_total {α : Type*} (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x) :
    variation μ = total μ := by
  unfold variation total Finsupp.sum
  exact Finset.sum_congr rfl (fun x _ => abs_of_nonneg (hμ x))

theorem distance_le_variations {α : Type*} (μ ν : Mass α) :
    distance μ ν ≤ variation μ + variation ν := by
  classical
  let S := μ.support ∪ ν.support
  rw [distance, variation_eq_sum _ (show (μ - ν).support ⊆ S from Finsupp.support_sub),
    variation_eq_sum μ (show μ.support ⊆ S from Finset.subset_union_left),
    variation_eq_sum ν (show ν.support ⊆ S from Finset.subset_union_right),
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  change |μ x - ν x| ≤ |μ x| + |ν x|
  simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (μ x) (-(ν x))

theorem distance_comm {α : Type*} (μ ν : Mass α) : distance μ ν = distance ν μ := by
  classical
  let S := μ.support ∪ ν.support
  have h1 : (μ - ν).support ⊆ S := Finsupp.support_sub
  have h2 : (ν - μ).support ⊆ S := by simpa [Finset.union_comm] using
    (Finsupp.support_sub (f := ν) (g := μ))
  rw [distance, distance, variation_eq_sum _ h1, variation_eq_sum _ h2]
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm _ _

theorem distance_le_totals {α : Type*} (μ ν : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x) : distance μ ν ≤ total μ + total ν := by
  simpa only [variation_eq_total μ hμ, variation_eq_total ν hν] using distance_le_variations μ ν

theorem distance_of_disjoint {α : Type*} (μ ν : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
    (hd : Disjoint μ.support ν.support) : distance μ ν = total μ + total ν := by
  classical
  let S := μ.support ∪ ν.support
  rw [distance, variation_eq_sum _ (show (μ - ν).support ⊆ S from Finsupp.support_sub),
    total_eq_sum μ (show μ.support ⊆ S from Finset.subset_union_left),
    total_eq_sum ν (show ν.support ⊆ S from Finset.subset_union_right),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  change |μ x - ν x| = μ x + ν x
  by_cases hx : μ x = 0
  · simp [hx, abs_of_nonneg (hν x)]
  · have hn : ν x = 0 := by
      apply Finsupp.notMem_support_iff.mp
      exact fun h => Finset.disjoint_left.mp hd (Finsupp.mem_support_iff.mpr hx) h
    simp [hn, abs_of_nonneg (hμ x)]

/-- Equal total masses make the L1 distance twice the pointwise deficit. -/
theorem distance_eq_twice_deficit {α : Type*} (μ ν δ : Mass α)
    (ht : total μ = total ν)
    (hp : ∀ x, |μ x - ν x| = μ x - ν x + 2 * δ x) :
    distance μ ν = 2 * total δ := by
  classical
  let S := μ.support ∪ ν.support ∪ δ.support
  have hμ : μ.support ⊆ S := fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hν : ν.support ⊆ S := fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hδ : δ.support ⊆ S := Finset.subset_union_right
  have hd : (μ - ν).support ⊆ S := Finsupp.support_sub.trans Finset.subset_union_left
  rw [distance, variation_eq_sum _ hd]
  simp only [Finsupp.sub_apply, hp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← total_eq_sum μ hμ, ← total_eq_sum ν hν, ← total_eq_sum δ hδ,
    ht, sub_self, zero_add]

/-- A negative translation has the same distance as the positive one. -/
theorem translation_distance_neg (μ : Mass ℤ) (h : ℤ) :
    distance (μ.mapDomain (fun z => z + -h)) μ =
      distance (μ.mapDomain (fun z => z + h)) μ := by
  have hi : Function.Injective (fun z : ℤ => z + h) := fun _ _ he => add_right_cancel he
  calc
    _ = distance ((μ.mapDomain (fun z => z + -h)).mapDomain (fun z => z + h))
        (μ.mapDomain (fun z => z + h)) := (distance_push_injective hi _ _).symm
    _ = distance μ (μ.mapDomain (fun z => z + h)) := by
      rw [← Finsupp.mapDomain_comp]
      have he : (fun z : ℤ => z + h) ∘ (fun z : ℤ => z + -h) = id := by
        funext z
        simp only [Function.comp_apply, neg_add_cancel_right, id_eq]
      rw [he, Finsupp.mapDomain_id]
    _ = _ := distance_comm _ _

/-- Passing an L1 comparison through a bounded test costs its sup bound. -/
theorem expectation_difference_bound {α : Type*} (μ ν : Mass α) (f : α → ℝ) (B : ℝ)
    (hf : ∀ x, |f x| ≤ B) : |expectation μ f - expectation ν f| ≤ B * distance μ ν := by
  have he : expectation (μ - ν) f = expectation μ f - expectation ν f :=
    Finsupp.sum_sub_index (fun _ a b => sub_mul a b _)
  rw [← he]
  unfold expectation distance variation Finsupp.sum
  calc
    |∑ x ∈ (μ - ν).support, (μ - ν) x * f x| ≤
        ∑ x ∈ (μ - ν).support, |(μ - ν) x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ (μ - ν).support, |(μ - ν) x| * B := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)
    _ = B * ∑ x ∈ (μ - ν).support, |(μ - ν) x| := by rw [← Finset.sum_mul, mul_comm]

end Hindman168.FiniteMass
