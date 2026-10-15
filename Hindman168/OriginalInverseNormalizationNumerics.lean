import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Uniform numerical choices for the original interval inverse interface.
The parameters below are chosen before the input period, interval length,
or bounded input function. No inverse assertion is assumed here. -/

namespace Hindman168

noncomputable def originalInverseLogParameter (δ : ℝ) : ℝ :=
  max 2 (-Real.log (δ / 4))

theorem originalInverseLogParameter_ge_two (δ : ℝ) :
    2 ≤ originalInverseLogParameter δ :=
  le_max_left _ _

theorem originalInverseLogParameter_nonneg (δ : ℝ) :
    0 ≤ originalInverseLogParameter δ :=
  le_trans (by norm_num) (originalInverseLogParameter_ge_two δ)

theorem originalInverseLogParameter_exp_le {δ : ℝ} (hδ : 0 < δ) :
    Real.exp (-originalInverseLogParameter δ) ≤ δ / 4 := by
  apply (Real.le_log_iff_exp_le (by positivity : 0 < δ / 4)).mp
  have h := neg_le_neg (le_max_right (2 : ℝ) (-Real.log (δ / 4)))
  simpa only [neg_neg, originalInverseLogParameter] using h

theorem originalInverse_exp_neg_one_le_half :
    Real.exp (-1 : ℝ) ≤ 1 / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    Real.exp (-1 : ℝ) = 1 / Real.exp 1 := by
      rw [Real.exp_neg, one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) htwo

noncomputable def originalInverseComplexityBudget (δ : ℝ) (C : ℕ) : ℝ :=
  (originalInverseLogParameter δ + 1 + C) ^ C

noncomputable def originalInverseCorrelationBudget (δ : ℝ) (C : ℕ) : ℝ :=
  Real.exp (-originalInverseComplexityBudget δ C)

theorem originalInverseComplexityBudget_nonneg (δ : ℝ) (C : ℕ) :
    0 ≤ originalInverseComplexityBudget δ C := by
  exact pow_nonneg (by
    have := originalInverseLogParameter_nonneg δ
    positivity) C

theorem originalInverseCorrelationBudget_pos (δ : ℝ) (C : ℕ) :
    0 < originalInverseCorrelationBudget δ C := Real.exp_pos _

theorem originalInverse_doubled_length_density {L : ℕ} (hL : 0 < L) :
    (L : ℝ) / (2 * L : ℕ) = 1 / 2 := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [Nat.cast_mul, Nat.cast_ofNat]
  field_simp

theorem originalInverse_doubled_length_density_lower {L : ℕ} (hL : 0 < L) :
    Real.exp (-1 : ℝ) ≤ (L : ℝ) / (2 * L : ℕ) := by
  rw [originalInverse_doubled_length_density hL]
  exact originalInverse_exp_neg_one_le_half

theorem originalInverse_doubled_length_no_wrap {L : ℕ} (hL : 0 < L) :
    2 * (L - 1) < 2 * L := by omega

end Hindman168
