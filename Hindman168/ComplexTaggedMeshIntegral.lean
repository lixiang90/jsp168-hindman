import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! A direct finite tagged-mesh approximation of a complex integral. The
error follows from the actual oscillation on each cell, not an assumed
Riemann convergence theorem. Tags need not lie inside their assigned cells. -/
namespace Hindman168
open MeasureTheory Set
open scoped BigOperators Interval

theorem complex_tagged_mesh_integral_error (N : ℕ) (hN : 0 < N)
    (tag : Fin N → ℝ) (g : ℝ → ℂ) (hg : Continuous g) (ε : ℝ)
    (hOsc : ∀ i : Fin N, ∀ t ∈ Icc ((i.val : ℝ)/N) (((i.val : ℝ)+1)/N),
      ‖g t-g (tag i)‖ ≤ ε) :
    ‖(∫ t in (0 : ℝ)..1, g t) - (∑ i : Fin N, g (tag i))/(N : ℂ)‖ ≤ ε := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hwidth (i : Fin N) : (((i.val : ℝ)+1)/N)-(i.val : ℝ)/N = 1/(N : ℝ) := by ring
  have hab (i : Fin N) : (i.val : ℝ)/N ≤ ((i.val : ℝ)+1)/N := by
    apply div_le_div_of_nonneg_right _ hNR.le
    linarith
  have hcell (i : Fin N) :
      ‖(∫ t in ((i.val : ℝ)/N)..(((i.val : ℝ)+1)/N), g t) - g (tag i)/(N : ℂ)‖ ≤ ε/N := by
    have he : (∫ t in ((i.val : ℝ)/N)..(((i.val : ℝ)+1)/N), g t-g (tag i)) =
        (∫ t in ((i.val : ℝ)/N)..(((i.val : ℝ)+1)/N), g t) - g (tag i)/(N : ℂ) := by
      rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, hwidth]
      simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
      congr 1
      ring
    rw [← he]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (i.val : ℝ)/N)
      (b := ((i.val : ℝ)+1)/N) (f := fun t => g t-g (tag i)) (C := ε) (by
        intro t ht
        rw [uIoc_of_le (hab i)] at ht
        exact hOsc i t ⟨ht.1.le,ht.2⟩)
    simpa only [hwidth, abs_of_pos (one_div_pos.mpr hNR), mul_one_div] using hb
  have hsum : (∑ i : Fin N, ∫ t in ((i.val : ℝ)/N)..(((i.val : ℝ)+1)/N), g t) =
      ∫ t in (0 : ℝ)..1, g t := by
    have hs := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ)/(N : ℝ)) (n := N) (f := g) (μ := volume)
      (fun _ _ => hg.intervalIntegrable _ _)
    rw [Fin.sum_univ_eq_sum_range (fun k => ∫ t in ((k : ℝ)/N)..(((k : ℝ)+1)/N), g t)]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, div_self hNR.ne'] using hs
  rw [← hsum, Finset.sum_div, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin N, ‖(∫ t in ((i.val : ℝ)/N)..(((i.val : ℝ)+1)/N), g t)-g (tag i)/(N : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, ε/(N : ℝ) := Finset.sum_le_sum (fun i _ => hcell i)
    _ = ε := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

end Hindman168
