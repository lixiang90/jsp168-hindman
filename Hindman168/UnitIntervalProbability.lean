import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! The actual length-one interval probability used for the point mixture. -/
namespace Hindman168
open MeasureTheory Set

noncomputable def unitIntervalProbability : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

theorem unit_interval_probability_isProbability : IsProbabilityMeasure unitIntervalProbability := by
  constructor
  simp only [unitIntervalProbability, Measure.restrict_apply_univ, Real.volume_Ioc,
    sub_zero, ENNReal.ofReal_one]

end Hindman168
