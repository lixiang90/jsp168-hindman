import Hindman168.HarmonicIntervalEventBound
import Hindman168.FiniteSupportedConditioning

/-! Multiplicative neighborhoods of the original cutoff endpoints have
mass at most `2*(log C + W/X)/(log X - W/X)`, for `1<C<=X`.
This retains the rough harmonic normalization rather than dropping units. -/

namespace Hindman168

open FiniteMass
open scoped BigOperators Classical

theorem rawMass_support_window (X W : ℕ) :
    (rawMass X W).support ⊆ harmonicWindow X W :=
  (intervalMass_support X (X ^ 2 : ℕ) W _).trans (unitInterval_raw X W).subset

theorem rawMass_lower_cutoff_band {X W : ℕ} {C : ℝ}
    (hX : 2 ≤ X) (hW : 0 < W) (hlog : (W : ℝ) / X < Real.log X) (hC : 1 < C) :
    event (rawMass X W) (fun p => (p : ℝ) < C * X) ≤
      (Real.log C + W / X) / (Real.log X - W / X) := by
  have hx : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have he := event_congr_on_support (rawMass X W)
    (fun p => (p : ℝ) < C * X) (fun p => (X : ℝ) ≤ p ∧ (p : ℝ) < C * X) (by
      intro p hp
      have hl := (Finset.mem_Ico.mp (Finset.mem_filter.mp (rawMass_support_window X W hp)).1).1
      have hlR : (X : ℝ) ≤ p := by exact_mod_cast hl
      simp only [hlR, true_and])
  rw [he]
  have hb := rawMass_interval_log_bound hX hW hlog hx
    (show (X : ℝ) < C * X by nlinarith)
  simpa only [mul_div_cancel_right₀ C hx.ne'] using hb

theorem rawMass_upper_cutoff_band {X W : ℕ} {C : ℝ}
    (hX : 2 ≤ X) (hW : 0 < W) (hlog : (W : ℝ) / X < Real.log X)
    (hC : 1 < C) (hCX : C ≤ X) :
    event (rawMass X W) (fun p => (X : ℝ) ^ 2 / C ≤ p) ≤
      (Real.log C + W / X) / (Real.log X - W / X) := by
  have hx : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hc : 0 < C := by linarith
  have ha : 0 < (X : ℝ) ^ 2 / C := div_pos (sq_pos_of_pos hx) hc
  have haX : (X : ℝ) ≤ (X : ℝ) ^ 2 / C := (le_div_iff₀ hc).mpr (by nlinarith)
  have he := event_congr_on_support (rawMass X W)
    (fun p => (X : ℝ) ^ 2 / C ≤ p)
    (fun p => (X : ℝ) ^ 2 / C ≤ p ∧ (p : ℝ) < (X : ℝ) ^ 2) (by
      intro p hp
      have hh := (Finset.mem_Ico.mp (Finset.mem_filter.mp (rawMass_support_window X W hp)).1).2
      have hhR : (p : ℝ) < (X : ℝ) ^ 2 := by exact_mod_cast hh
      simp only [hhR, and_true])
  rw [he]
  have hb := rawMass_interval_log_bound hX hW hlog ha
    (show (X : ℝ) ^ 2 / C < (X : ℝ) ^ 2 from (div_lt_iff₀ hc).mpr (by nlinarith [sq_pos_of_pos hx]))
  have hr : (X : ℝ) ^ 2 / ((X : ℝ) ^ 2 / C) = C := by field_simp
  rw [hr] at hb
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hlog).le
  exact add_le_add le_rfl (div_le_div_of_nonneg_left (Nat.cast_nonneg W) hx haX)

theorem rawMass_cutoff_bands {X W : ℕ} {C : ℝ}
    (hX : 2 ≤ X) (hW : 0 < W) (hlog : (W : ℝ) / X < Real.log X)
    (hC : 1 < C) (hCX : C ≤ X) :
    event (rawMass X W) (fun p => (p : ℝ) < C * X ∨ (X : ℝ) ^ 2 / C ≤ p) ≤
      2 * ((Real.log C + W / X) / (Real.log X - W / X)) := by
  have hn (p : ℕ) : 0 ≤ rawMass X W p := by
    rw [rawMass_apply]
    exact harmonicWeight_nonneg (harmonicNormalizer_pos hX hW hlog) p
  have hu := event_or_le_add (rawMass X W) (fun p => (p : ℝ) < C * X)
    (fun p => (X : ℝ) ^ 2 / C ≤ p) hn
  have hlo := rawMass_lower_cutoff_band hX hW hlog hC
  have hhi := rawMass_upper_cutoff_band hX hW hlog hC hCX
  linarith

end Hindman168
