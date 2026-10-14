import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hindman168

theorem finite_natural_span_card (s : Finset ℕ) (hs : s.Nonempty) :
    (s.card : ℝ) ≤ (s.max' hs : ℝ)-(s.min' hs : ℝ)+1 := by
  have hsub : s ⊆ Finset.Icc (s.min' hs) (s.max' hs) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨s.min'_le n hn, s.le_max' n hn⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hlo := s.min'_le_max' hs
  have hcast : ((s.max' hs+1-s.min' hs : ℕ) : ℝ) =
      (s.max' hs : ℝ)-(s.min' hs : ℝ)+1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    ring
  rw [← hcast]
  exact_mod_cast hc

theorem finite_integer_span_card (s : Finset ℤ) (hs : s.Nonempty) :
    (s.card : ℝ) ≤ (s.max' hs : ℝ)-(s.min' hs : ℝ)+1 := by
  have hsub : s ⊆ Finset.Icc (s.min' hs) (s.max' hs) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨s.min'_le n hn, s.le_max' n hn⟩
  have hc := Finset.card_le_card hsub
  have he := Int.card_Icc_of_le (s.min' hs) (s.max' hs) (show s.min' hs ≤ s.max' hs+1 by
    have := s.min'_le_max' hs
    omega)
  have hcr : (s.card : ℝ) ≤ ((Finset.Icc (s.min' hs) (s.max' hs)).card : ℝ) := by
    exact_mod_cast hc
  have her := congrArg (fun z : ℤ => (z : ℝ)) he
  push_cast at her
  linarith

end Hindman168
