import Hindman168.IntegerIntervalCubeZeroExtension
import Hindman168.CyclicIntervalPositiveNormTransfer

/-! The exact zero-extension bridge at the dyadic-root level.

Positive-dimensional interval values are nonnegative. In dimension zero
both existing definitions are signed cube means, not norms; the ratio
identity remains valid by the exponent-one identity. All interval
normalisation statements below require a nonempty interval explicitly.
No inverse theorem is assumed or asserted. -/

namespace Hindman168
open scoped Classical

/-- In dimension zero the existing interval value is the signed cube mean.
No nonnegativity statement is made in this dimension. -/
theorem integerIntervalPeriodicGowersValue_zero_dimension (q L : ℕ)
    (v : ZMod q → ℝ) :
    integerIntervalPeriodicGowersValue q 0 L v =
      integerIntervalPeriodicCubeMean q 0 L v := by
  simp [integerIntervalPeriodicGowersValue]

/-- The indicator has a strictly positive rooted cyclic value in every
dimension, including zero. -/
theorem intervalPeriodicZeroExtension_indicator_gowers_pos {q M d L : ℕ}
    [NeZero M] (hL : 0 < L) (hM : 2 * (L - 1) < M) :
    0 < subgroupGowersValue (⊤ : AddSubgroup (ZMod M)) d
      (intervalPeriodicZeroExtension q M L (fun _ => 1)) := by
  exact Real.rpow_pos_of_pos
    (intervalPeriodicZeroExtension_indicator_cube_pos (q := q) (d := d) hL hM) _

/-- Exact normalisation at the rooted-value level. The positive-dimensional
case uses proved positivity of cyclic cube averages; dimension zero is
handled separately as the signed exponent-one case. -/
theorem integerIntervalPeriodicGowersValue_eq_zeroExtension_ratio {q M d L : ℕ}
    [NeZero M] (hL : 0 < L) (hM : 2 * (L - 1) < M) (v : ZMod q → ℝ) :
    integerIntervalPeriodicGowersValue q d L v =
      subgroupGowersValue (⊤ : AddSubgroup (ZMod M)) d
        (intervalPeriodicZeroExtension q M L v) /
      subgroupGowersValue (⊤ : AddSubgroup (ZMod M)) d
        (intervalPeriodicZeroExtension q M L (fun _ => 1)) := by
  by_cases hd : d = 0
  · subst d
    simpa only [integerIntervalPeriodicGowersValue, subgroupGowersValue,
      pow_zero, Nat.cast_one, inv_one, Real.rpow_one] using
        integerIntervalPeriodicCubeMean_eq_zeroExtension_ratio hL hM v
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    unfold integerIntervalPeriodicGowersValue subgroupGowersValue
    rw [integerIntervalPeriodicCubeMean_eq_zeroExtension_ratio (M := M) hL hM v]
    exact Real.div_rpow
      (subgroupCubeAverage_nonneg (⊤ : AddSubgroup (ZMod M)) d hdpos _)
      (intervalPeriodicZeroExtension_indicator_cube_pos (q := q) (d := d) hL hM).le _

/-- An all-input nonnegativity consequence, with positive dimension and
positive interval length rather than an unproved cube-mean premise. -/
theorem integerIntervalPeriodicGowersValue_nonneg_of_pos {q d L : ℕ}
    (hd : 0 < d) (hL : 0 < L) (v : ZMod q → ℝ) :
    0 ≤ integerIntervalPeriodicGowersValue q d L v :=
  integerIntervalPeriodicGowersValue_nonneg q d L v
    (integerIntervalPeriodicCubeMean_nonneg_of_pos hd hL v)

/-- The dyadic power recovers the actual cube mean for every real periodic
input in positive dimension on a nonempty interval. -/
theorem integerIntervalPeriodicGowersValue_pow_of_pos {q d L : ℕ}
    (hd : 0 < d) (hL : 0 < L) (v : ZMod q → ℝ) :
    integerIntervalPeriodicGowersValue q d L v ^ (2 ^ d) =
      integerIntervalPeriodicCubeMean q d L v :=
  integerIntervalPeriodicGowersValue_pow q d L v
    (integerIntervalPeriodicCubeMean_nonneg_of_pos hd hL v)

/-- Exact threshold conversion with the positive indicator normalisation
factor retained. This is only an arithmetic equivalence, not an inverse
or correlation assertion. -/
theorem integerIntervalPeriodicGowersValue_threshold_iff {q M d L : ℕ}
    [NeZero M] (hL : 0 < L) (hM : 2 * (L - 1) < M)
    (v : ZMod q → ℝ) (δ : ℝ) :
    δ ≤ integerIntervalPeriodicGowersValue q d L v ↔
      δ * subgroupGowersValue (⊤ : AddSubgroup (ZMod M)) d
        (intervalPeriodicZeroExtension q M L (fun _ => 1)) ≤
      subgroupGowersValue (⊤ : AddSubgroup (ZMod M)) d
        (intervalPeriodicZeroExtension q M L v) := by
  rw [integerIntervalPeriodicGowersValue_eq_zeroExtension_ratio (M := M) hL hM v]
  exact le_div_iff₀
    (intervalPeriodicZeroExtension_indicator_gowers_pos (q := q) (d := d) hL hM)

end Hindman168
