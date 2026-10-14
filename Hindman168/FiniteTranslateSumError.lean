import Hindman168.FiniteHaarIdentities
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace Hindman168
open scoped BigOperators Classical

theorem finite_unit_sum_abs_le_card {A : Type*} (s : Finset A) (f : A → ℝ)
    (hf : ∀ a, |f a| ≤ 1) : |∑ a ∈ s, f a| ≤ s.card := by
  calc
    _ ≤ ∑ a ∈ s, |f a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ s, (1 : ℝ) := Finset.sum_le_sum (fun a _ => hf a)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Only the two set-difference tails contribute to a finite unit-test
sum difference; their common intersection cancels exactly. -/
theorem finite_unit_sum_difference_bound {A : Type*} [DecidableEq A]
    (s t : Finset A) (f : A → ℝ)
    (hf : ∀ a, |f a| ≤ 1) :
    |(∑ a ∈ s, f a) - ∑ a ∈ t, f a| ≤ ((s \ t).card : ℝ) + ((t \ s).card : ℝ) := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff]
  exact (abs_sub _ _).trans (add_le_add (finite_unit_sum_abs_le_card _ f hf)
    (finite_unit_sum_abs_le_card _ f hf))

/-- A finite translated sum differs from the original sum only by
points whose forward or backward translates leave the original set. -/
theorem finite_translate_sum_difference_bound {G : Type*} [AddCommGroup G] [DecidableEq G]
    (s : Finset G) (r : G) (f : G → ℝ) (hf : ∀ a, |f a| ≤ 1) :
    |(∑ a ∈ s, f (a + r)) - ∑ a ∈ s, f a| ≤
      ((s.filter (fun a => a + r ∉ s)).card : ℝ) +
        ((s.filter (fun a => a - r ∉ s)).card : ℝ) := by
  let T := s.map (Equiv.addRight r).toEmbedding
  have hmem (a : G) : a ∈ T ↔ a - r ∈ s := by
    constructor
    · intro ha
      obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp ha
      change b + r = a at hba
      simpa only [← hba, add_sub_cancel_right] using hb
    · intro ha
      exact Finset.mem_map.mpr ⟨a - r, ha, sub_add_cancel a r⟩
  have hfront : (T \ s).card ≤ (s.filter (fun a => a + r ∉ s)).card := by
    apply Finset.card_le_card_of_injOn (fun a => a - r)
    · intro a ha
      obtain ⟨hT, hnot⟩ := Finset.mem_sdiff.mp ha
      exact Finset.mem_filter.mpr ⟨(hmem a).mp hT, by simpa only [sub_add_cancel] using hnot⟩
    · intro a _ b _ he
      have hh := congrArg (fun x : G => x + r) he
      simpa only [sub_add_cancel] using hh
  have hback : s \ T = s.filter (fun a => a - r ∉ s) := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_filter, hmem]
  have hsum : (∑ a ∈ T, f a) = ∑ a ∈ s, f (a + r) := by
    simp only [T, Finset.sum_map, Equiv.coe_toEmbedding]
    rfl
  rw [← hsum]
  have hb := finite_unit_sum_difference_bound T s f hf
  rw [hback] at hb
  exact hb.trans (add_le_add (by exact_mod_cast hfront) le_rfl)

end Hindman168
