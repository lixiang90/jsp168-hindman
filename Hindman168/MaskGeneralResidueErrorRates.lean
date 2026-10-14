import Hindman168.MaskTargetResidueErrorRates
import Hindman168.MaskGeneralResidueAverage

/-! General target-row version under |F_root| ≤ 1 + ν.
The original sampling laws and retained majorants remain unchanged.
All error estimates are proved from the source parameters. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

include ha hC in
theorem source_targetRootRest_progression_uniform_majorized
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ rowMajorant gap C t label w none y) :
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
  filter_upwards [source_targetRootRest_progression_error_majorized gap a ha C hC t htail label F hroot, hg]
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
