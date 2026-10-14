import Hindman168.UniformIntervals

/-!
# Exact L1 translation distance for uniform integer intervals

The signed shift is reduced to its natural absolute value. The number of
exposed points is exactly min(T,|u|), so the formula works also for shifts
longer than the interval. The starting point is any integer.
-/

namespace Hindman168

open scoped Classical

theorem integerWindow_shift (A : ℤ) (T : ℕ) (u : ℤ) :
    (integerWindow A T).image (fun z => z + u) = integerWindow (A + u) T := by
  ext z
  simp only [integerWindow, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨y, hy, rfl⟩
    omega
  · intro hz
    exact ⟨z - u, by omega, by omega⟩

theorem uniformIntervalMass_shift (A : ℤ) (T : ℕ) (u : ℤ) :
    (uniformIntervalMass A T).mapDomain (fun z => z + u) = uniformIntervalMass (A + u) T := by
  unfold uniformIntervalMass
  rw [FiniteMass.uniformFinsetMass_push _ _ (fun _ _ h => add_right_cancel h)]
  congr 1
  ext z
  simp only [integerWindow, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨y, hy, rfl⟩
    omega
  · intro hz
    exact ⟨z - u, by omega, by omega⟩

theorem uniformIntervalPMF_shift (A : ℤ) {T : ℕ} (hT : 0 < T) (u : ℤ) :
    (uniformIntervalPMF A T hT).map (fun z => z + u) = uniformIntervalPMF (A + u) T hT := by
  ext z
  rw [uniformIntervalPMF, FiniteMass.toPMF_map_apply, uniformIntervalMass_shift,
    uniformIntervalPMF, FiniteMass.toPMF_apply]

theorem integerWindow_positive_shift_sdiff (A : ℤ) (T H : ℕ) :
    integerWindow A T \ integerWindow (A + H) T = integerWindow A (min T H) := by
  ext z
  simp only [integerWindow, Finset.mem_sdiff, Finset.mem_Ico]
  by_cases hTH : T ≤ H
  · rw [min_eq_left hTH]
    omega
  · rw [min_eq_right (by omega : H ≤ T)]
    omega

theorem uniform_interval_positive_shift_distance (A : ℤ) (T H : ℕ) :
    FiniteMass.distance ((uniformIntervalMass A T).mapDomain (fun z => z + (H : ℤ)))
      (uniformIntervalMass A T) = 2 * ((min T H : ℕ) : ℝ) / T := by
  classical
  rw [uniformIntervalMass_shift, FiniteMass.distance_comm]
  unfold uniformIntervalMass FiniteMass.uniformFinsetMass
  rw [integerWindow_card, integerWindow_card]
  have h := FiniteMass.flatMass_equal_card_distance (integerWindow A T) (integerWindow (A + H) T)
    (c := (T : ℝ)⁻¹) (inv_nonneg.mpr (Nat.cast_nonneg _))
    (by rw [integerWindow_card, integerWindow_card])
  rw [h]
  rw [div_eq_mul_inv]
  congr 2
  norm_cast
  trans (integerWindow A (min T H)).card
  · congr 1
    ext z
    simp only [integerWindow, Finset.mem_sdiff, Finset.mem_Ico]
    by_cases hTH : T ≤ H
    · rw [min_eq_left hTH]
      omega
    · rw [min_eq_right (by omega : H ≤ T)]
      omega
  · exact integerWindow_card A (min T H)

theorem uniform_interval_translation_distance (A : ℤ) (T : ℕ) (u : ℤ) :
    FiniteMass.distance ((uniformIntervalMass A T).mapDomain (fun z => z + u))
      (uniformIntervalMass A T) = 2 * ((min T u.natAbs : ℕ) : ℝ) / T := by
  let f : ℤ → ℝ := fun h =>
    FiniteMass.distance ((uniformIntervalMass A T).mapDomain (fun z => z + h)) (uniformIntervalMass A T)
  change f u = _
  rcases (Int.natAbs_eq_iff.mp (rfl : u.natAbs = u.natAbs)) with he | he
  · exact (congrArg f he).trans (uniform_interval_positive_shift_distance A T u.natAbs)
  · exact (congrArg f he).trans
      ((FiniteMass.translation_distance_neg (uniformIntervalMass A T) (u.natAbs : ℤ)).trans
        (uniform_interval_positive_shift_distance A T u.natAbs))

theorem min_nat_ratio {T : ℕ} (hT : 0 < T) (H : ℕ) :
    2 * ((min T H : ℕ) : ℝ) / T = 2 * min (1 : ℝ) ((H : ℝ) / T) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  by_cases hHT : H ≤ T
  · have hratio : (H : ℝ) / T ≤ 1 := (div_le_iff₀ hTr).mpr (by
      simp only [one_mul]
      exact_mod_cast hHT)
    rw [min_eq_right hHT, min_eq_right hratio]
    ring
  · have hTH : T ≤ H := by omega
    have hratio : (1 : ℝ) ≤ (H : ℝ) / T := (le_div_iff₀ hTr).mpr (by
      simp only [one_mul]
      exact_mod_cast hTH)
    rw [min_eq_left hTH, min_eq_left hratio]
    field_simp

theorem uniform_interval_translation_paper_formula (A : ℤ) {T : ℕ} (hT : 0 < T) (u : ℤ) :
    FiniteMass.distance ((uniformIntervalMass A T).mapDomain (fun z => z + u))
      (uniformIntervalMass A T) = 2 * min (1 : ℝ) (|(u : ℝ)| / T) := by
  rw [uniform_interval_translation_distance, min_nat_ratio hT]
  have he : (u.natAbs : ℝ) = |(u : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [he]

theorem uniform_interval_translation_linear (A : ℤ) {T : ℕ} (hT : 0 < T) (u : ℤ) :
    FiniteMass.distance ((uniformIntervalMass A T).mapDomain (fun z => z + u))
      (uniformIntervalMass A T) ≤ 2 * |(u : ℝ)| / T := by
  rw [uniform_interval_translation_paper_formula A hT u]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 2)

end Hindman168
