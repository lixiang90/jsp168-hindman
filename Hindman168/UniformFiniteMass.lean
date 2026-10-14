import Hindman168.FiniteProbability
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Constant finite masses and uniform finite probability laws

Fiber coefficients are counts with the original constant weight. Injective
maps preserve uniform laws. For equal-size supports the L1 distance is
twice the mass of one exposed set difference.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

noncomputable def flatMass {α : Type*} (S : Finset α) (c : ℝ) : Mass α :=
  Finsupp.onFinset S (fun x => if x ∈ S then c else 0) (by
    intro x hx
    by_contra ho
    exact hx (if_neg ho))

theorem flatMass_apply {α : Type*} (S : Finset α) (c : ℝ) (x : α) :
    flatMass S c x = if x ∈ S then c else 0 := rfl

theorem flatMass_support {α : Type*} (S : Finset α) (c : ℝ) :
    (flatMass S c).support ⊆ S := Finsupp.support_onFinset_subset

theorem flatMass_nonneg {α : Type*} (S : Finset α) {c : ℝ} (hc : 0 ≤ c) (x : α) :
    0 ≤ flatMass S c x := by
  rw [flatMass_apply]
  split_ifs
  · exact hc
  · exact le_rfl

theorem flatMass_total {α : Type*} (S : Finset α) (c : ℝ) :
    total (flatMass S c) = (S.card : ℝ) * c := by
  rw [total_eq_sum _ (flatMass_support S c)]
  simp only [flatMass_apply, Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]

theorem flatMass_push_coeff {α β : Type*} (S : Finset α) (c : ℝ) (f : α → β) (b : β) :
    (flatMass S c).mapDomain f b = ((S.filter (fun a => f a = b)).card : ℝ) * c := by
  rw [push_apply, Finset.sum_subset (flatMass_support S c) (by
    intro a _ ha
    rw [Finsupp.notMem_support_iff.mp ha]
    split_ifs <;> rfl)]
  have he : ∀ a ∈ S, (if b = f a then flatMass S c a else 0) = if f a = b then c else 0 := by
    intro a ha
    rw [flatMass_apply, if_pos ha]
    simp only [eq_comm]
  rw [Finset.sum_congr rfl he, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]

theorem flatMass_push_injective {α β : Type*} (S : Finset α) (c : ℝ)
    (f : α → β) (hf : Function.Injective f) :
    (flatMass S c).mapDomain f = flatMass (S.image f) c := by
  ext b
  rw [flatMass_apply]
  by_cases hb : b ∈ S.image f
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    rw [Finsupp.mapDomain_apply hf, flatMass_apply, if_pos ha,
      if_pos (Finset.mem_image.mpr ⟨a, ha, rfl⟩)]
  · rw [if_neg hb, flatMass_push_coeff]
    have he : S.filter (fun a => f a = b) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro a ha hab
      exact hb (Finset.mem_image.mpr ⟨a, ha, hab⟩)
    simp only [he, Finset.card_empty, Nat.cast_zero, zero_mul]

theorem flatMass_equal_card_distance {α : Type*} (S T : Finset α) {c : ℝ}
    (hc : 0 ≤ c) (hcard : S.card = T.card) :
    distance (flatMass S c) (flatMass T c) = 2 * ((S \ T).card : ℝ) * c := by
  rw [distance_comm]
  have h := distance_eq_twice_deficit (flatMass T c) (flatMass S c) (flatMass (S \ T) c)
    (by rw [flatMass_total, flatMass_total, hcard])
  rw [h, flatMass_total]
  · ring
  · intro x
    simp only [flatMass_apply, Finset.mem_sdiff]
    by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;>
      simp [hs, ht, abs_of_nonneg hc, abs_of_nonpos (neg_nonpos.mpr hc)]; ring

noncomputable def uniformFinsetMass {α : Type*} (S : Finset α) : Mass α :=
  flatMass S (S.card : ℝ)⁻¹

theorem uniformFinsetMass_nonneg {α : Type*} (S : Finset α) (x : α) :
    0 ≤ uniformFinsetMass S x := flatMass_nonneg S (inv_nonneg.mpr (Nat.cast_nonneg _)) x

theorem uniformFinsetMass_total {α : Type*} (S : Finset α) (hS : 0 < S.card) :
    total (uniformFinsetMass S) = 1 := by
  rw [uniformFinsetMass, flatMass_total]
  exact mul_inv_cancel₀ (by exact_mod_cast hS.ne')

noncomputable def uniformFinsetPMF {α : Type*} (S : Finset α) (hS : 0 < S.card) : PMF α :=
  toPMF (uniformFinsetMass S) (uniformFinsetMass_nonneg S) (uniformFinsetMass_total S hS)

theorem uniformFinsetPMF_apply {α : Type*} (S : Finset α) (hS : 0 < S.card) (x : α) :
    uniformFinsetPMF S hS x = ENNReal.ofReal (if x ∈ S then (S.card : ℝ)⁻¹ else 0) := rfl

theorem uniformFinsetMass_push {α β : Type*} (S : Finset α) (f : α → β)
    (hf : Function.Injective f) :
    (uniformFinsetMass S).mapDomain f = uniformFinsetMass (S.image f) := by
  rw [uniformFinsetMass, flatMass_push_injective S _ f hf, uniformFinsetMass,
    Finset.card_image_of_injective S hf]

end Hindman168.FiniteMass
