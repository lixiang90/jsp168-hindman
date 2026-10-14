import Hindman168.MaskRootOriginalMoments

/-! The enlarged-array means are the actual profile products under the
original conditional prime law, original harmonic pivots, quotient pairs
and two independent root intervals. No law or coefficient is replaced by
an assumed independent model. Regrouping profiles into B*H^j is separate. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskRootOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

local notation "S" => maskRootOriginalSampling m gap a ha C hC t J hJ hgap
local notation "d" => rootMomentDimension m gap t

noncomputable def profileProduct
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (U : Finset (Fin (Fintype.card (MaskRootCopiedRow m gap t)))) (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (z : Fin (m + 1) → ℤ) (v : MaskOriginalDirection m gap t → ℤ × ℤ) (u : ℤ × ℤ) : ℝ :=
  ∏ k ∈ U, MaskOriginalSampling.rowMajorant gap C t label w
    (rootSmoothedRowEnumeration d k).val.1.val.1
    ((MaskOriginalSampling.additiveData gap a C t w x).translatedForm
      (rootSmoothedRowEnumeration d k).val.1.val.1 (rootSmoothedRowEnumeration d k).val.1.val.2
      (fun col => z col + MaskOriginalSampling.rootShift gap a C t w x
        (rootPairValues u (rootSmoothedRowEnumeration d k).val.2) col) (predictionPairValues v))

noncomputable def profileAverage
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (U : Finset (Fin (Fintype.card (MaskRootCopiedRow m gap t)))) (w : ℕ) : ℝ :=
  expectation (conditionMass (masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val))
    (maskGeneratedCopiedPrimeGood m gap t w)) (fun x =>
      expectation (maskOriginalBaseMass m gap C w) (fun z =>
        expectation (directionPairMass gap t J w x) (fun v =>
          expectation (MaskOriginalSampling.rootMass (m := m) gap w) (fun u₀ =>
            expectation (MaskOriginalSampling.rootMass (m := m) gap w)
              (fun u₁ => profileProduct gap a C t label U w x z v (u₀, u₁))))))

include ha hC in
theorem profile_product_eventually
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (U : Finset (Fin (Fintype.card (MaskRootCopiedRow m gap t)))) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ z v u,
      (∏ k ∈ U, (1 + (S).weight ((S).labels label) (S).rows w k x
        (rootSmoothedSampleCoordinates z v u))) = profileProduct gap a C t label U w x z v u := by
  filter_upwards [coefficient_eval_eventually gap a ha C hC t] with w he
  intro x hx z v u
  unfold profileProduct
  apply Finset.prod_congr rfl
  intro k _
  let r := rootSmoothedRowEnumeration d k
  change (1 + integerDivisorMask (tailMass (primorial w)
    ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w r.val.1.val.1)))
      (∑ j, maskRootCopiedCoefficient m gap a C t w x r j * rootSmoothedSampleCoordinates z v u j)) =
    MaskOriginalSampling.rowMajorant gap C t label w r.val.1.val.1
      ((MaskOriginalSampling.additiveData gap a C t w x).translatedForm r.val.1.val.1 r.val.1.val.2
        (fun col => z col + MaskOriginalSampling.rootShift gap a C t w x (rootPairValues u r.val.2) col)
        (predictionPairValues v))
  exact congrArg (fun q : ℤ => 1 + integerDivisorMask (tailMass (primorial w)
    ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w r.val.1.val.1))) q)
      (he x hx z v u r)

theorem fullMajorant_eq_profileAverage_eventually
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (U : Finset (Fin (Fintype.card (MaskRootCopiedRow m gap t)))) :
    ∀ᶠ w in atTop, (S).fullMajorant label U w = profileAverage gap a C t J label U w := by
  filter_upwards [profile_product_eventually gap a ha C hC t J hJ hgap label U] with w he
  unfold MaskRootCopiedSampling.fullMajorant MaskRootCopiedSampling.normalizedMajorant profileAverage
  apply expectation_congr_support
  intro x hx
  have hxG := conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) x hx
  rw [sampling_law gap a ha C hC t J hJ hgap w x]
  apply congrArg (expectation (maskOriginalBaseMass m gap C w))
  funext z
  apply congrArg (expectation (directionPairMass gap t J w x))
  funext v
  apply congrArg (expectation (MaskOriginalSampling.rootMass (m := m) gap w))
  funext u₀
  apply congrArg (expectation (MaskOriginalSampling.rootMass (m := m) gap w))
  funext u₁
  exact he x hxG z v (u₀, u₁)

include ha hC hJ hgap in
theorem profileAverage_tendsto
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (U : Finset (Fin (Fintype.card (MaskRootCopiedRow m gap t)))) :
    Tendsto (profileAverage gap a C t J label U) atTop (𝓝 (((2 ^ U.card : ℕ) : ℝ))) := by
  exact (fullMajorant_tendsto gap a ha C hC t J hJ hgap htail label U).congr'
    (fullMajorant_eq_profileAverage_eventually gap a ha C hC t J hJ hgap label U)

end Hindman168.MaskRootOriginalSampling
