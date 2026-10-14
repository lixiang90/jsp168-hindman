import Hindman168.IntegerIntervalCubeCardBounds

namespace Hindman168

/-- A floor-width genuine parameter box retains the full interval scale.
The box only bounds cardinality; the domain still contains signed increments. -/
theorem integerIntervalCubeDomain_card_real_lower (d L : ℕ) (hL : d + 1 ≤ L) :
    ((L : ℝ) / (2 * ((d : ℝ) + 1))) ^ (d + 1) ≤
      ((integerIntervalCubeDomain d L).card : ℝ) := by
  have hn : 0 < d + 1 := Nat.succ_pos d
  have hH : 1 ≤ L / (d + 1) := (Nat.le_div_iff_mul_le hn).mpr (by simpa)
  have hmod := Nat.mod_lt L hn
  have hdecomp := Nat.mod_add_div L (d + 1)
  have hscale : L ≤ 2 * (d + 1) * (L / (d + 1)) := by nlinarith
  have hr : (L : ℝ) ≤ 2 * ((d : ℝ) + 1) * (L / (d + 1) : ℕ) := by
    exact_mod_cast hscale
  have hhalf : (L : ℝ) / (2 * ((d : ℝ) + 1)) ≤ (L / (d + 1) : ℕ) :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hbox : ((L / (d + 1) : ℕ) : ℝ) ^ (d + 1) ≤
      ((integerIntervalCubeDomain d L).card : ℝ) := by
    exact_mod_cast integerIntervalCubeDomain_card_lower_box d L (L / (d + 1))
      (Nat.mul_div_le L (d + 1))
  exact (pow_le_pow_left₀ (by positivity) hhalf (d + 1)).trans hbox

end Hindman168
