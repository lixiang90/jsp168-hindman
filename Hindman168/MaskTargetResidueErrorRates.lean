import Hindman168.MaskTargetResidueAverage

/-! A uniform rapid error for removing the actual progression restriction.
The factor k in the unnormalized class law is bounded by the actual pool
cap and is retained in the cubic sampling-size budget. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter Asymptotics
open scoped Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def targetRootResidueErrorCap (w : ℕ) : ℝ :=
  4 * (samplingSize (primorial w) (targetRootMultiplierCap gap t w) 0
    ((maskGeneratedMaster m gap).auxiliary w (gap w).val) : ℝ) ^ 3 /
    ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootOtherColumn gap t)))

noncomputable def targetRootResidueTestErrorCap (w : ℕ) : ℝ :=
  rootCubeBound gap t w * targetRootResidueErrorCap gap C t w

theorem targetRootResidueTestErrorCap_nonneg (w : ℕ) :
    0 ≤ targetRootResidueTestErrorCap gap C t w := by
  unfold targetRootResidueTestErrorCap rootCubeBound targetRootResidueErrorCap
  positivity

include hC in
theorem targetRootResidueErrorCap_rapid
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col) :
    RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (targetRootResidueErrorCap gap C t) := by
  have hD := powerDominates_log_to_cutoff
    (targetRootMultiplier_sampling_log_growth gap C hC t hgap (targetRootOtherColumn gap t))
  have hg := sampling_eventually_geometry hD
  apply rapid_of_polynomial_majorant hD
    (hg.mono (fun w hw => by exact_mod_cast (by omega : 0 < (maskGeneratedMaster m gap).cutoff w
      ((C w).pivot (targetRootOtherColumn gap t)))))
    (Eventually.of_forall (fun w => ⟨by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
        ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val), by
      exact_mod_cast (samplingSize_bounds (primorial w) (targetRootMultiplierCap gap t w) 0
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val)).2.2.2.2⟩))
    3 (by norm_num : (0 : ℝ) < 4)
  filter_upwards [hg] with w hw
  unfold targetRootResidueErrorCap
  rw [abs_of_nonneg (by positivity)]

include hC in
theorem targetRootResidueTestErrorCap_rapid
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col) :
    RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (targetRootResidueTestErrorCap gap C t) :=
  (targetRootResidueErrorCap_rapid gap C hC t hgap).mul_power
    (Eventually.of_forall (fun w => by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
        ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val)))
    (2 * 2 ^ Fintype.card (MaskOriginalDirection m gap t))

include ha hC in
theorem source_targetRootRest_progression_uniform
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ v,
      |expectation (rootRestMass gap C t w) (fun rest =>
          expectation (integerProgressionMass
            ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t))) (primorial w)
            (targetRootMultiplier gap t x) (targetRootOffset gap a C t w x rest v))
            (rootCubeTest gap t F w x v)) -
        expectation (integerMass
          ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t))) (primorial w))
          (rootCubeTest gap t F w x v)| ≤ targetRootResidueTestErrorCap gap C t w := by
  have hg := sampling_eventually_geometry (powerDominates_log_to_cutoff
    (targetRootMultiplier_sampling_log_growth gap C hC t hgap (targetRootOtherColumn gap t)))
  filter_upwards [source_targetRootRest_progression_error gap a ha C hC t htail label F hroot, hg]
    with w he hw
  intro x hx v
  let Q : ℝ := samplingSize (primorial w) (targetRootMultiplierCap gap t w) 0
    ((maskGeneratedMaster m gap).auxiliary w (gap w).val)
  have hs := samplingSize_bounds (primorial w) (targetRootMultiplierCap gap t w) 0
    ((maskGeneratedMaster m gap).auxiliary w (gap w).val)
  have hQ : 2 ≤ Q := by dsimp [Q]; exact_mod_cast hs.1
  have hkQ : (targetRootMultiplier gap t x : ℝ) ≤ Q := by
    dsimp [Q]
    exact_mod_cast (targetRootMultiplier_le_cap gap t w x hx).trans hs.2.2.1
  have hr := residueError_polynomial (K := targetRootMultiplier gap t x) (Q := Q)
    hw.1 hw.2.1 hQ (by dsimp [Q]; exact_mod_cast hs.2.1) hkQ
  have hkr : (targetRootMultiplier gap t x : ℝ) * residueError
      ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootOtherColumn gap t)))
      (primorial w) (targetRootMultiplier gap t x) ≤ targetRootResidueErrorCap gap C t w := by
    calc
      _ ≤ Q * (4 * Q ^ 2 / ((maskGeneratedMaster m gap).cutoff w
          ((C w).pivot (targetRootOtherColumn gap t)))) :=
        mul_le_mul hkQ hr.2 hr.1 (by linarith : 0 ≤ Q)
      _ = _ := by unfold targetRootResidueErrorCap; dsimp [Q]; ring
  apply (he x hx v).trans
  unfold targetRootResidueTestErrorCap
  calc
    _ = rootCubeBound gap t w * ((targetRootMultiplier gap t x : ℝ) * residueError
        ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootOtherColumn gap t)))
        (primorial w) (targetRootMultiplier gap t x)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hkr (by unfold rootCubeBound; positivity)

end Hindman168.MaskOriginalSampling
