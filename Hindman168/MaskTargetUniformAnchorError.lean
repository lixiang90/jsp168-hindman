import Hindman168.MaskTargetRootOffsetGrowth

/-! A uniform actual anchor error, including the full centered-mask cube
sup bound. Its rapid decay follows from original parameter growth and the
supported offset theorem, rather than an assumed negligible error. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter Asymptotics
open scoped Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def targetRootTestErrorCap (w : ℕ) : ℝ :=
  rootCubeBound gap t w * targetRootAffineErrorCap gap C t w

include hC in
theorem targetRootTestErrorCap_rapid
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col) :
    RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (targetRootTestErrorCap gap C t) := by
  exact (targetRootAffineErrorCap_rapid gap C hC t hgap).mul_power
    (Eventually.of_forall (fun w => by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
        ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val)))
    (2 * 2 ^ Fintype.card (MaskOriginalDirection m gap t))

include hC in
theorem targetRootTestErrorCap_eventually_nonneg
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col) :
    ∀ᶠ w in atTop, 0 ≤ targetRootTestErrorCap gap C t w := by
  have hg := sampling_eventually_geometry (powerDominates_log_to_cutoff
    (targetRootOffset_sampling_log_growth gap C hC t hgap))
  filter_upwards [hg] with w hw
  have hl : 0 < Real.log ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t)) : ℝ) :=
    lt_of_lt_of_le (by norm_num) (sampling_log_lower hw.1)
  unfold targetRootTestErrorCap rootCubeBound targetRootAffineErrorCap affineRootErrorCap
  positivity

include hC in
theorem targetRootTestErrorCap_weighted_tendsto_zero
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col) (q : ℕ) :
    Tendsto (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q *
      targetRootTestErrorCap gap C t w) atTop (𝓝 0) := by
  apply (isLittleO_one_iff ℝ).mp
  simpa only [pow_zero, inv_one] using
    ((targetRootTestErrorCap_rapid gap C hC t hgap).mul_power
      (Eventually.of_forall (fun w => by
        exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
          ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val))) q) 0

include ha hC in
theorem source_targetCube_uniform_anchor_comparison
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1)
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
  filter_upwards [source_targetCube_anchor_comparison gap a ha C hC t hgap htail label F hroot,
    targetRootOffset_supported_bound gap a ha C hC t J,
    targetRoot_arithmetic_eventually gap a ha C hC t, hg] with w hc hh hk hw
  intro x hx rest v hr hv
  exact (hc x hx rest v).trans (mul_le_mul_of_nonneg_left
    (affineRootError_le_cap hw.1 hw.2.1 (hk x hx).1
      (targetRootMultiplier_le_cap gap t w x hx) (hh x hx rest v hr hv))
    (by unfold rootCubeBound; positivity))

end Hindman168.MaskOriginalSampling
