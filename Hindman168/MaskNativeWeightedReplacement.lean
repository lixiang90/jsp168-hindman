import Hindman168.MaskNativeWeightedVariance
import Hindman168.FiniteReplicaJointLaw

/-! Actual source target-cube domination and weighted replacement under
the original joint law. The centered root test supplies |G|<=B; desired
variance, mean and positivity conclusions are derived from source data. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskRootOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

noncomputable def nativeG
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) (p : NativeMomentPoint m gap t) : ℝ :=
  MaskOriginalSampling.targetCube gap a C t F w (p.1, p.2.1) p.2.2

theorem nativeJointMass_support_good (w : ℕ) (p : NativeMomentPoint m gap t)
    (hp : p ∈ (nativeJointMass gap C t J w).support) :
    maskGeneratedCopiedPrimeGood m gap t w p.1 := by
  apply conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) p.1
  apply Finsupp.mem_support_iff.mpr
  intro he
  apply Finsupp.mem_support_iff.mp hp
  unfold nativeJointMass
  rw [conditionalJoint_apply, he, zero_mul]

include hC in
theorem source_nativeG_eventually_domination
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1) :
    ∀ᶠ w in atTop, ∀ p ∈ (nativeJointMass gap C t J w).support,
      |nativeG gap a C t F w p| ≤ nativeB gap C t a label w p := by
  filter_upwards [MaskOriginalSampling.masks_eventually_bounded gap C hC t htail label, hroot]
    with w hm hr
  intro p hp
  have hx := nativeJointMass_support_good gap C t J w p hp
  unfold nativeG nativeB targetMajorantCube MaskOriginalSampling.targetCube
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
  intro η _
  let y := (maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerLinearForm p.1
    (masterColumnCoefficient N a (fun w => (C w).block) w) (maskGeneratedRowDataFamily m gap t).target p.2.1 +
    ((maskGeneratedRowDataFamily m gap t).rows.translationModulus (maskGeneratedMaster m gap) w p.1
      (maskGeneratedRowDataFamily m gap t).target : ℤ) * ∑ k, predictionPairValues p.2.2 k (η k)
  change |F w p.1 none y| ≤ MaskOriginalSampling.rowMajorant gap C t label w none y
  rw [congrFun (hr p.1 hx) y]
  have hn := (hm none y).1
  simpa only [MaskOriginalSampling.rowMajorant, abs_of_nonneg hn, abs_one, add_comm] using
    abs_sub (integerDivisorMask (tailMass (primorial w)
      ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y) (1 : ℝ)

include ha hC hJ hgap in
theorem source_native_weighted_replacement_tendsto_zero
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1) :
    Tendsto (fun w => expectation (nativeJointMass gap C t J w) (fun p => nativeG gap a C t F w p *
      (nativeH gap C t a label w p - retainedMeanConstant m gap t))) atTop (𝓝 0) := by
  apply weighted_centered_replacement_tendsto_zero
    (nativeJointMass gap C t J) (nativeG gap a C t F) (nativeB gap C t a label) (nativeH gap C t a label)
    (retainedMeanConstant m gap t) (((2 ^ (2 ^ rootMomentDimension m gap t) : ℕ) : ℝ))
    (nativeJointMass_eventually_nonneg gap C t J hC)
    (source_nativeG_eventually_domination gap a C hC t J htail label F hroot)
  · exact (targetMajorantAverage_tendsto gap a ha C hC t J hJ hgap htail label).congr
      (fun w => (nativeB_average_eq gap C t J a label w).symm)
  · exact nativeVariance_tendsto_zero gap a ha C hC t J hJ hgap htail label

include ha hC hJ hgap in
theorem source_native_terminal_replacement_tendsto_zero
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1) :
    Tendsto (fun w => expectation (nativeJointMass gap C t J w)
      (fun p => nativeG gap a C t F w p * nativeH gap C t a label w p) -
        retainedMeanConstant m gap t * expectation (nativeJointMass gap C t J w) (nativeG gap a C t F w))
      atTop (𝓝 0) :=
  (source_native_weighted_replacement_tendsto_zero gap a ha C hC t J hJ hgap htail label F hroot).congr
    (fun _ => expectation_centered_product_eq _ _ _ _)

end Hindman168.MaskRootOriginalSampling
