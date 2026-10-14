import Hindman168.MaskTargetUniformAnchorError
import Hindman168.MaskGeneralAnchorComparison

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
theorem source_targetCube_uniform_anchor_comparison_majorized
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ rowMajorant gap C t label w none y)
    (J : ℕ) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ rest v,
      rest ∈ (rootRestMass gap C t w).support →
      v ∈ (MaskRootOriginalSampling.directionPairMass gap t J w x).support →
      |expectation
          (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t))) (primorial w))
          (fun y => targetCube gap a C t F w (x, insertPivotCoordinate (targetRootAnchor gap t) rest y) v) -
        expectation (integerProgressionMass
          ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t))) (primorial w)
          (targetRootMultiplier gap t x) (targetRootOffset gap a C t w x rest v))
          (rootCubeTest gap t F w x v)| ≤ targetRootTestErrorCap gap C t w := by
  have hg := sampling_eventually_geometry (powerDominates_log_to_cutoff
    (targetRootOffset_sampling_log_growth gap C hC t hgap))
  filter_upwards [source_targetCube_anchor_comparison_majorized gap a ha C hC t hgap htail label F hroot,
    targetRootOffset_supported_bound gap a ha C hC t J,
    targetRoot_arithmetic_eventually gap a ha C hC t, hg] with w hc hh hk hw
  intro x hx rest v hr hv
  exact (hc x hx rest v).trans (mul_le_mul_of_nonneg_left
    (affineRootError_le_cap hw.1 hw.2.1 (hk x hx).1
      (targetRootMultiplier_le_cap gap t w x hx) (hh x hx rest v hr hv))
    (by unfold rootCubeBound; positivity))

end Hindman168.MaskOriginalSampling
