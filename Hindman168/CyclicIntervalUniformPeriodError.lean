import Hindman168.CyclicIntervalCubeTransfer

namespace Hindman168
open scoped Classical

theorem integerIntervalPeriodicCubeMean_abs_le_one (q d L : ℕ) (hL : 0 < L)
    (f : ZMod q → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |integerIntervalPeriodicCubeMean q d L f| ≤ 1 := by
  have hc : (0 : ℝ) < (integerIntervalCubeDomain d L).card := by
    exact_mod_cast (integerIntervalCubeDomain_nonempty d L hL).card_pos
  rw [integerIntervalPeriodicCubeMean, abs_div, abs_of_pos hc, div_le_one hc]
  exact finite_unit_sum_abs_le_card _ _ (integerPeriodicCubeProduct_abs_le_one q d f hf)

theorem integerIntervalCubeTransferConstant_lower (d : ℕ) :
    2 * ((d : ℝ) + 1) ≤ integerIntervalCubeTransferConstant d := by
  have hA : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hB : 1 ≤ (2 * ((d : ℝ) + 1)) ^ (d + 1) :=
    one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) d])
  have hAB : 1 ≤ (2 : ℝ) ^ d * (2 * ((d : ℝ) + 1)) ^ (d + 1) := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hAB (show 0 ≤ 2 * ((d : ℝ) + 1) by positivity)
  unfold integerIntervalCubeTransferConstant
  nlinarith

/-- Uniform in every positive number of periods. For the small-period
range, unit bounds suffice; the geometric estimate treats the other range. -/
theorem integerIntervalPeriodicCubeMean_all_period_error (q d K : ℕ) [NeZero q]
    (hK : 0 < K) (f : ZMod q → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |integerIntervalPeriodicCubeMean q d (K * q) f -
        subgroupCubeAverage (⊤ : AddSubgroup (ZMod q)) d f| ≤
      integerIntervalCubeTransferConstant d / K := by
  by_cases hlarge : d + 1 ≤ K
  · exact integerIntervalPeriodicCubeMean_period_error q d K hlarge f hf
  · have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hKr : (0 : ℝ) < K := by exact_mod_cast hK
    have hsmall : (K : ℝ) ≤ (d : ℝ) + 1 := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hlarge))
    have htwo : (2 : ℝ) ≤ integerIntervalCubeTransferConstant d / K := by
      apply (le_div_iff₀ hKr).mpr
      linarith [integerIntervalCubeTransferConstant_lower d]
    have ha := integerIntervalPeriodicCubeMean_abs_le_one q d (K * q) (Nat.mul_pos hK hq) f hf
    have hb := subgroupCubeAverage_abs_le_one (⊤ : AddSubgroup (ZMod q)) d f hf
    exact ((abs_sub _ _).trans ((add_le_add ha hb).trans_eq (by norm_num))).trans htwo

end Hindman168
