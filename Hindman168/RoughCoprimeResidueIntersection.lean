import Hindman168.AlignmentClassCounts
import Mathlib.Tactic.Ring

namespace Hindman168

theorem rough_coprime_residue_pair (t K : ℕ) (hcop : t.Coprime K) (a u : ℤ) :
    ∃ c : ℤ, ∀ x : ℤ,
      (Int.ModEq t a x ∧ Int.ModEq K u x) ↔ Int.ModEq (t * K : ℕ) c x := by
  obtain ⟨y, hy⟩ := Int.mod_coprime hcop
  let c : ℤ := a + (t : ℤ) * (y * (u - a))
  have ht : Int.ModEq t a c := by simp [c]
  have hK : Int.ModEq K u c := by
    have hr := (hy.mul_right (u - a)).add_left a
    have hc : Int.ModEq K c u := by
      change Int.ModEq K (a + (t : ℤ) * (y * (u - a))) u
      convert hr using 1 <;> ring
    exact hc.symm
  refine ⟨c, ?_⟩
  intro x
  have hm := Int.modEq_and_modEq_iff_modEq_mul (a := c) (b := x)
    (m := (t : ℤ)) (n := (K : ℤ)) (by simpa using hcop)
  rw [← Nat.cast_mul] at hm
  constructor
  · rintro ⟨hx, hu⟩
    exact hm.mp ⟨ht.symm.trans hx, hK.symm.trans hu⟩
  · intro hx
    obtain ⟨hxT, hxK⟩ := hm.mpr hx
    exact ⟨ht.trans hxT, hK.trans hxK⟩

theorem rough_coprime_interval_class_intersection (A B a u : ℤ) (t K : ℕ)
    (hcop : t.Coprime K) :
    ∃ c : ℤ, alignmentIntervalClass A B t a ∩ alignmentIntervalClass A B K u =
      alignmentIntervalClass A B (t * K : ℕ) c := by
  classical
  obtain ⟨c, hc⟩ := rough_coprime_residue_pair t K hcop a u
  refine ⟨c, ?_⟩
  ext x
  simp only [Finset.mem_inter, alignmentIntervalClass, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hx, ht⟩, ⟨_, hK⟩⟩
    exact ⟨hx, (hc x).mp ⟨ht, hK⟩⟩
  · rintro ⟨hx, hm⟩
    obtain ⟨ht, hK⟩ := (hc x).mpr hm
    exact ⟨⟨hx, ht⟩, ⟨hx, hK⟩⟩

theorem rough_coprime_interval_intersection_count (A B a u : ℤ) (t K : ℕ)
    (ht : 0 < t) (hK : 0 < K) (hcop : t.Coprime K) (hAB : A ≤ B) :
    |((alignmentIntervalClass A B t a ∩ alignmentIntervalClass A B K u).card : ℝ) -
      ((B : ℝ) - A) / (t * K : ℕ)| ≤ 1 := by
  obtain ⟨c, hc⟩ := rough_coprime_interval_class_intersection A B a u t K hcop
  rw [hc]
  exact alignment_interval_class_count A B c (t * K) (Nat.mul_pos ht hK) hAB

end Hindman168
