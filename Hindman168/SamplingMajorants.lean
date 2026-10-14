import Hindman168.HarmonicTranslation
import Hindman168.ProductLaw

/-!
# Polynomial majorants for the finite harmonic sampling errors

These bounds do not replace the sharp finite estimates. They expose the
growth needed for uniform little-o estimates at all inverse-power scales.
-/

namespace Hindman168

theorem sampling_log_lower {X : ℕ} (hX : 4 ≤ X) : (1 : ℝ) ≤ Real.log X := by
  have h := Real.le_log_one_add_of_nonneg (x := (3 : ℝ)) (by norm_num)
  norm_num at h
  have h4 : Real.log 4 ≤ Real.log X := Real.log_le_log (by norm_num) (by exact_mod_cast hX)
  linarith

theorem sampling_denominator_lower {X W : ℕ} (hX : 4 ≤ X) (hWX : 2 * W ≤ X) :
    Real.log X / 2 ≤ Real.log X - (W : ℝ) / X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hWXr : (2 : ℝ) * W ≤ X := by exact_mod_cast hWX
  have hw : (W : ℝ) / X ≤ 1 / 2 := (div_le_iff₀ hXR).mpr (by linarith)
  have hl := sampling_log_lower hX
  linarith

theorem sampling_denominator_pos {X W : ℕ} (hX : 4 ≤ X) (hWX : 2 * W ≤ X) :
    (W : ℝ) / X < Real.log X := by
  have hl := sampling_log_lower hX
  have hd := sampling_denominator_lower hX hWX
  linarith

theorem residueError_polynomial {X W K : ℕ} {Q : ℝ}
    (hX : 4 ≤ X) (hWX : 2 * W ≤ X) (hQ : 2 ≤ Q)
    (hWQ : (W : ℝ) ≤ Q) (hKQ : (K : ℝ) ≤ Q) :
    0 ≤ residueError X W K ∧ residueError X W K ≤ 4 * Q ^ 2 / X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hdpos := sub_pos.mpr (sampling_denominator_pos hX hWX)
  have hdlow : (1 : ℝ) / 2 ≤ Real.log X - (W : ℝ) / X := by
    have hl := sampling_log_lower hX
    have hd := sampling_denominator_lower hX hWX
    linarith
  constructor
  · unfold residueError
    positivity
  · unfold residueError
    rw [Nat.cast_add, Nat.cast_one]
    apply (div_le_iff₀ (mul_pos hXR hdpos)).mpr
    have hn : (W : ℝ) * (K + 1 : ℝ) ≤ 2 * Q ^ 2 := by
      have hk : (K : ℝ) + 1 ≤ 2 * Q := by linarith
      have hm := mul_le_mul hWQ hk (by positivity : (0 : ℝ) ≤ K + 1)
        (by linarith : 0 ≤ Q)
      nlinarith
    have he : 4 * Q ^ 2 / X * ((X : ℝ) * (Real.log X - (W : ℝ) / X)) =
        4 * Q ^ 2 * (Real.log X - (W : ℝ) / X) := by field_simp
    rw [he]
    nlinarith [sq_nonneg Q]

theorem translationError_polynomial {X W H : ℕ} {Q : ℝ}
    (hX : 4 ≤ X) (hWX : 2 * W ≤ X) (hQ : 2 ≤ Q) (hHQ : (H : ℝ) ≤ Q) :
    0 ≤ 2 * (H : ℝ) / (X * (Real.log X - (W : ℝ) / X)) ∧
      2 * (H : ℝ) / (X * (Real.log X - (W : ℝ) / X)) ≤ 4 * Q / X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hdpos := sub_pos.mpr (sampling_denominator_pos hX hWX)
  have hdlow : (1 : ℝ) / 2 ≤ Real.log X - (W : ℝ) / X := by
    have hl := sampling_log_lower hX
    have hd := sampling_denominator_lower hX hWX
    linarith
  constructor
  · positivity
  · apply (div_le_iff₀ (mul_pos hXR hdpos)).mpr
    have he : 4 * Q / X * ((X : ℝ) * (Real.log X - (W : ℝ) / X)) =
        4 * Q * (Real.log X - (W : ℝ) / X) := by field_simp
    rw [he]
    nlinarith

theorem dilationError_polynomial {X W K : ℕ} {Q : ℝ}
    (hX : 4 ≤ X) (hWX : 2 * W ≤ X) (hK : 1 ≤ K) (hQ : 2 ≤ Q)
    (hWQ : (W : ℝ) ≤ Q) (hKQ : (K : ℝ) ≤ Q) :
    0 ≤ dilationError X W K ∧ dilationError X W K ≤ 8 * Q ^ 2 / Real.log X := by
  have hXr : (4 : ℝ) ≤ X := by exact_mod_cast hX
  have hXR : (0 : ℝ) < X := by linarith
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hQpos : 0 < Q := by linarith
  have hl := sampling_log_lower hX
  have hlpos : 0 < Real.log X := by linarith
  have hd := sampling_denominator_lower hX hWX
  have hdpos := sub_pos.mpr (sampling_denominator_pos hX hWX)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hKr
  have hlogKupper : Real.log K ≤ K := Real.log_le_self (by positivity)
  have hWK : (W : ℝ) * K ≤ Q ^ 2 := by
    have hm := mul_le_mul hWQ hKQ (Nat.cast_nonneg K) hQpos.le
    nlinarith
  have hdiv : (W : ℝ) * K / X ≤ Q ^ 2 := by
    apply (div_le_iff₀ hXR).mpr
    nlinarith [sq_nonneg Q]
  have hinv : (1 : ℝ) / X ≤ 1 := (div_le_iff₀ hXR).mpr (by linarith)
  have hterm : ((W : ℝ) * K / X) * (1 + 1 / X) ≤ 2 * Q ^ 2 := by
    have hm := mul_le_mul hdiv (show 1 + 1 / (X : ℝ) ≤ 2 by linarith)
      (by positivity : (0 : ℝ) ≤ 1 + 1 / X) (sq_nonneg Q)
    nlinarith
  have hn : 2 * Real.log K + ((W : ℝ) * K / X) * (1 + 1 / X) ≤ 4 * Q ^ 2 := by
    nlinarith
  constructor
  · unfold dilationError
    positivity
  · unfold dilationError
    calc
      _ ≤ 4 * Q ^ 2 / (Real.log X - (W : ℝ) / X) :=
        div_le_div_of_nonneg_right hn hdpos.le
      _ ≤ 4 * Q ^ 2 / (Real.log X / 2) :=
        div_le_div_of_nonneg_left (by positivity) (half_pos hlpos) hd
      _ = 8 * Q ^ 2 / Real.log X := by field_simp; norm_num

end Hindman168
