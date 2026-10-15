import Hindman168.CyclicIntervalPositiveNormTransfer

/-! Empty intervals cannot satisfy a positive original inverse threshold.
The totalized definitions are evaluated at zero, without cancellation. -/

namespace Hindman168

@[simp] theorem originalInverse_integerIntervalCubeDomain_zero (d : ℕ) :
    integerIntervalCubeDomain d 0 = ∅ := by
  simp [integerIntervalCubeDomain]

@[simp] theorem originalInverse_integerIntervalPeriodicCubeMean_zero
    (q d : ℕ) (v : ZMod q → ℝ) :
    integerIntervalPeriodicCubeMean q d 0 v = 0 := by
  simp [integerIntervalPeriodicCubeMean]

@[simp] theorem originalInverse_integerIntervalPeriodicGowersValue_zero
    (q d : ℕ) (v : ZMod q → ℝ) :
    integerIntervalPeriodicGowersValue q d 0 v = 0 := by
  have hp : (((2 ^ d : ℕ) : ℝ)⁻¹) ≠ 0 := by positivity
  simp only [integerIntervalPeriodicGowersValue,
    originalInverse_integerIntervalPeriodicCubeMean_zero, Real.zero_rpow hp]

theorem originalInverse_interval_length_positive {q d L : ℕ}
    (v : ZMod q → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hnorm : δ / 4 ≤ integerIntervalPeriodicGowersValue q d L v) :
    0 < L := by
  by_contra hL
  have hz : L = 0 := by omega
  subst L
  rw [originalInverse_integerIntervalPeriodicGowersValue_zero] at hnorm
  linarith

theorem originalInverse_period_count_positive {q d K : ℕ}
    (v : ZMod q → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hnorm : δ / 4 ≤ integerIntervalPeriodicGowersValue q d (K * q) v) :
    0 < K := by
  have hlength := originalInverse_interval_length_positive v hδ hnorm
  by_contra hK
  have hz : K = 0 := by omega
  simp [hz] at hlength

end Hindman168
