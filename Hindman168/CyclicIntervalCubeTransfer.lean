import Hindman168.IntegerIntervalPeriodicMean
import Hindman168.IntegerIntervalCubeRealLowerBound

namespace Hindman168
open scoped Classical

/-- One explicit dimension-only constant for the cube-power transfer. -/
noncomputable def integerIntervalCubeTransferConstant (d : ℕ) : ℝ :=
  2 * (2 : ℝ) ^ d * ((d : ℝ) + 1) * (2 * ((d : ℝ) + 1)) ^ (d + 1)

theorem integerIntervalCubeTransferConstant_pos (d : ℕ) :
    0 < integerIntervalCubeTransferConstant d := by
  unfold integerIntervalCubeTransferConstant
  positivity

theorem integerIntervalPeriodicCubeMean_scaled_error (q d L : ℕ) [NeZero q]
    (hL : d + 1 ≤ L) (f : ZMod q → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |integerIntervalPeriodicCubeMean q d L f -
        subgroupCubeAverage (⊤ : AddSubgroup (ZMod q)) d f| ≤
      integerIntervalCubeTransferConstant d * q / L := by
  have hLp : 0 < L := lt_of_lt_of_le (Nat.succ_pos d) hL
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLp
  have hc : (0 : ℝ) < (integerIntervalCubeDomain d L).card := by
    exact_mod_cast (integerIntervalCubeDomain_nonempty d L hLp).card_pos
  have hden : (0 : ℝ) < ((L : ℝ) / (2 * ((d : ℝ) + 1))) ^ (d + 1) := by positivity
  have hD : (((d + 1) * (q - 1) : ℕ) : ℝ) ≤ ((d : ℝ) + 1) * q := by
    exact_mod_cast Nat.mul_le_mul_left (d + 1) (Nat.sub_le q 1)
  have hnum : 2 * (2 : ℝ) ^ d * ((d + 1) * (q - 1) : ℕ) * (L : ℝ) ^ d ≤
      2 * (2 : ℝ) ^ d * (((d : ℝ) + 1) * q) * (L : ℝ) ^ d :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hD (by positivity)) (by positivity)
  calc
    _ ≤ (2 * (2 : ℝ) ^ d * ((d + 1) * (q - 1) : ℕ) * (L : ℝ) ^ d) /
        (integerIntervalCubeDomain d L).card :=
      integerIntervalPeriodicCubeMean_cyclic_error q d L hLp f hf
    _ ≤ (2 * (2 : ℝ) ^ d * (((d : ℝ) + 1) * q) * (L : ℝ) ^ d) /
        (integerIntervalCubeDomain d L).card := div_le_div_of_nonneg_right hnum hc.le
    _ ≤ (2 * (2 : ℝ) ^ d * (((d : ℝ) + 1) * q) * (L : ℝ) ^ d) /
        (((L : ℝ) / (2 * ((d : ℝ) + 1))) ^ (d + 1)) :=
      div_le_div_of_nonneg_left (by positivity) hden
        (integerIntervalCubeDomain_card_real_lower d L hL)
    _ = integerIntervalCubeTransferConstant d * q / L := by
      unfold integerIntervalCubeTransferConstant
      rw [div_pow, pow_succ]
      field_simp

/-- The paper's O_d(1/K) estimate, with its dimension-only constant
and all cyclic moduli and unit inputs quantified explicitly. -/
theorem integerIntervalPeriodicCubeMean_period_error (q d K : ℕ) [NeZero q]
    (hK : d + 1 ≤ K) (f : ZMod q → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |integerIntervalPeriodicCubeMean q d (K * q) f -
        subgroupCubeAverage (⊤ : AddSubgroup (ZMod q)) d f| ≤
      integerIntervalCubeTransferConstant d / K := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hKp : 0 < K := lt_of_lt_of_le (Nat.succ_pos d) hK
  have hL : d + 1 ≤ K * q := hK.trans (by nlinarith)
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hKp.ne'
  have hb := integerIntervalPeriodicCubeMean_scaled_error q d (K * q) hL f hf
  have he : integerIntervalCubeTransferConstant d * (q : ℝ) / (K * q : ℕ) =
      integerIntervalCubeTransferConstant d / K := by
    rw [Nat.cast_mul]
    field_simp
  exact hb.trans_eq he

end Hindman168
