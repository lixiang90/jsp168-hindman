import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic

namespace Hindman168

theorem rough_ceiling_index_monotone (D : ℕ) (hD : 0 < D) :
    Monotone (fun i : ℕ => i ⌈/⌉ D) := (gc_mul_ceilDiv hD).monotone_l

theorem rough_ceiling_index_add (D : ℕ) (hD : 0 < D) (i j : ℕ) :
    (i+j) ⌈/⌉ D ≤ i ⌈/⌉ D+j ⌈/⌉ D := by
  apply (ceilDiv_le_iff_le_mul hD).mpr
  have hi : i ≤ D*(i ⌈/⌉ D) := (ceilDiv_le_iff_le_mul hD).mp le_rfl
  have hj : j ≤ D*(j ⌈/⌉ D) := (ceilDiv_le_iff_le_mul hD).mp le_rfl
  nlinarith

theorem rough_ceiling_index_initial (D : ℕ) (hD : 0 < D) (i : ℕ) (hi : i ≤ D) :
    i ⌈/⌉ D ≤ 1 := by
  apply (ceilDiv_le_iff_le_mul hD).mpr
  simpa only [mul_one] using hi

theorem rough_ceiling_index_positive (D : ℕ) (hD : 0 < D) (i : ℕ) (hi : 0 < i) :
    0 < i ⌈/⌉ D := by
  have h : i ≤ D*(i ⌈/⌉ D) := (ceilDiv_le_iff_le_mul hD).mp le_rfl
  by_contra! hz
  have he : i ⌈/⌉ D = 0 := by omega
  rw [he, mul_zero] at h
  omega

theorem rough_ceiling_index_one (D : ℕ) (hD : 0 < D) : 1 ⌈/⌉ D = 1 := by
  have hlo := rough_ceiling_index_positive D hD 1 (by omega)
  have hhi := rough_ceiling_index_initial D hD 1 hD
  omega

theorem rough_ceiling_index_mul (D : ℕ) (hD : 0 < D) (s : ℕ) : (s*D) ⌈/⌉ D = s := by
  apply le_antisymm
  · apply (ceilDiv_le_iff_le_mul hD).mpr
    nlinarith
  · have h : s*D ≤ D*((s*D) ⌈/⌉ D) := (ceilDiv_le_iff_le_mul hD).mp le_rfl
    nlinarith

theorem rough_ceiling_index_terminal (D : ℕ) (hD : 0 < D) (s : ℕ) :
    s+1 ≤ (s*D+1) ⌈/⌉ D := by
  have h : s*D+1 ≤ D*((s*D+1) ⌈/⌉ D) := (ceilDiv_le_iff_le_mul hD).mp le_rfl
  by_contra! hz
  have he : (s*D+1) ⌈/⌉ D ≤ s := by omega
  have hmul := Nat.mul_le_mul_left D he
  nlinarith

end Hindman168
