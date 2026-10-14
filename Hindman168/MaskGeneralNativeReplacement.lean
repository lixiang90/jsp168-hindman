import Hindman168.MaskNativeWeightedReplacement

/-! General target-row version under |F_root| ≤ 1 + ν.
The original sampling laws and retained majorants remain unchanged.
All error estimates are proved from the source parameters. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskRootOriginalSampling

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

theorem source_nativeG_eventually_domination_majorized
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ MaskOriginalSampling.rowMajorant gap C t label w none y) :
    ∀ᶠ w in atTop, ∀ p ∈ (nativeJointMass gap C t J w).support,
      |nativeG gap a C t F w p| ≤ nativeB gap C t a label w p := by
  filter_upwards [hroot] with w hr
  intro p hp
  have hx := nativeJointMass_support_good gap C t J w p hp
  unfold nativeG nativeB targetMajorantCube MaskOriginalSampling.targetCube
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
  intro η _
  exact hr p.1 hx _


include ha hC hJ hgap in
theorem source_native_weighted_replacement_tendsto_zero_majorized
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ MaskOriginalSampling.rowMajorant gap C t label w none y) :
    Tendsto (fun w => expectation (nativeJointMass gap C t J w) (fun p => nativeG gap a C t F w p *
      (nativeH gap C t a label w p - retainedMeanConstant m gap t))) atTop (𝓝 0) := by
  apply weighted_centered_replacement_tendsto_zero
    (nativeJointMass gap C t J) (nativeG gap a C t F) (nativeB gap C t a label) (nativeH gap C t a label)
    (retainedMeanConstant m gap t) (((2 ^ (2 ^ rootMomentDimension m gap t) : ℕ) : ℝ))
    (nativeJointMass_eventually_nonneg gap C t J hC)
    (source_nativeG_eventually_domination_majorized gap a C t J label F hroot)
  · exact (targetMajorantAverage_tendsto gap a ha C hC t J hJ hgap htail label).congr
      (fun w => (nativeB_average_eq gap C t J a label w).symm)
  · exact nativeVariance_tendsto_zero gap a ha C hC t J hJ hgap htail label

include ha hC hJ hgap in
theorem source_native_terminal_replacement_tendsto_zero_majorized
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ MaskOriginalSampling.rowMajorant gap C t label w none y) :
    Tendsto (fun w => expectation (nativeJointMass gap C t J w)
      (fun p => nativeG gap a C t F w p * nativeH gap C t a label w p) -
        retainedMeanConstant m gap t * expectation (nativeJointMass gap C t J w) (nativeG gap a C t F w))
      atTop (𝓝 0) :=
  (source_native_weighted_replacement_tendsto_zero_majorized gap a ha C hC t J hJ hgap htail label F hroot).congr
    (fun _ => expectation_centered_product_eq _ _ _ _)

end Hindman168.MaskRootOriginalSampling
