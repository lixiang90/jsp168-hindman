import Hindman168.MaskNativeMomentLaw
import Hindman168.FiniteRootMixedMoments

/-! The first and second enlarged profiles are exactly the native
original E B H and E B H^2. Their power-of-two limits use no extra
moment, independence or normalization assumption. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskRootOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

local notation "d" => rootMomentDimension m gap t

include ha hC in
theorem profile_first_average_eq_eventually
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, profileAverage gap a C t J label (rootMomentFirst d) w =
      nativeFirstMoment gap C t J a label w := by
  filter_upwards [profile_first_product_eventually gap a ha C hC t label] with w hw
  unfold profileAverage nativeFirstMoment
  rw [expectation_nativeJointMass]
  apply expectation_congr_support
  intro x hx
  have hxG := conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) x hx
  apply congrArg (expectation (maskOriginalBaseMass m gap C w))
  funext z
  apply congrArg (expectation (directionPairMass gap t J w x))
  funext v
  have he : (fun u₀ => expectation (MaskOriginalSampling.rootMass (m := m) gap w)
      (fun u₁ => profileProduct gap a C t label (rootMomentFirst d) w x z v (u₀, u₁))) =
      (fun u₀ => expectation (MaskOriginalSampling.rootMass (m := m) gap w)
        (fun _u₁ => targetMajorantCube gap a C t label w x z v *
          shiftedRetainedProfile gap a C t label w x z v u₀)) := by
    funext u₀
    apply congrArg (expectation (MaskOriginalSampling.rootMass (m := m) gap w))
    exact funext (fun u₁ => hw x hxG z v (u₀, u₁))
  rw [he, expectation_unused_root_weight _ (MaskOriginalSampling.rootMass_probability gap w).2,
    nativeH_root_expectation_eq]
  rfl

include ha hC in
theorem profile_second_average_eq_eventually
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, profileAverage gap a C t J label (rootMomentSecond d) w =
      nativeSecondMoment gap C t J a label w := by
  filter_upwards [profile_second_product_eventually gap a ha C hC t label] with w hw
  unfold profileAverage nativeSecondMoment
  rw [expectation_nativeJointMass]
  apply expectation_congr_support
  intro x hx
  have hxG := conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) x hx
  apply congrArg (expectation (maskOriginalBaseMass m gap C w))
  funext z
  apply congrArg (expectation (directionPairMass gap t J w x))
  funext v
  have he : (fun u₀ => expectation (MaskOriginalSampling.rootMass (m := m) gap w)
      (fun u₁ => profileProduct gap a C t label (rootMomentSecond d) w x z v (u₀, u₁))) =
      (fun u₀ => expectation (MaskOriginalSampling.rootMass (m := m) gap w)
        (fun u₁ => targetMajorantCube gap a C t label w x z v *
          shiftedRetainedProfile gap a C t label w x z v u₀ *
          shiftedRetainedProfile gap a C t label w x z v u₁)) := by
    funext u₀
    apply congrArg (expectation (MaskOriginalSampling.rootMass (m := m) gap w))
    exact funext (fun u₁ => hw x hxG z v (u₀, u₁))
  rw [he, expectation_root_weighted_square, nativeH_root_expectation_eq]
  rfl

include ha hC hJ hgap in
theorem nativeFirstMoment_tendsto
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    Tendsto (nativeFirstMoment gap C t J a label) atTop
      (𝓝 (((2 ^ (2 ^ d + d * 2 ^ (d - 1)) : ℕ) : ℝ))) := by
  have ht := profileAverage_tendsto gap a ha C hC t J hJ hgap htail label (rootMomentFirst d)
  have hc := congrArg (fun q : ℕ => Tendsto (profileAverage gap a C t J label (rootMomentFirst d))
    atTop (𝓝 (((2 ^ q : ℕ) : ℝ)))) (rootMomentFirst_card d)
  exact (hc.mp ht).congr' (profile_first_average_eq_eventually gap a ha C hC t J label)

include ha hC hJ hgap in
theorem nativeSecondMoment_tendsto
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    Tendsto (nativeSecondMoment gap C t J a label) atTop
      (𝓝 (((2 ^ (2 ^ d + 2 * (d * 2 ^ (d - 1))) : ℕ) : ℝ))) := by
  have ht := profileAverage_tendsto gap a ha C hC t J hJ hgap htail label (rootMomentSecond d)
  have hc := congrArg (fun q : ℕ => Tendsto (profileAverage gap a C t J label (rootMomentSecond d))
    atTop (𝓝 (((2 ^ q : ℕ) : ℝ)))) (rootMomentSecond_card d)
  exact (hc.mp ht).congr' (profile_second_average_eq_eventually gap a ha C hC t J label)

end Hindman168.MaskRootOriginalSampling
