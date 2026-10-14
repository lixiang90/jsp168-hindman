import Hindman168.MaskRootMomentProfileLaw

/-! The target-only enlarged subsystem is exactly the paper's B under
the actual original normalized joint law, and E B tends to 2^(2^d).
The two unused independent root variables integrate to one. -/

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

noncomputable def targetMajorantCube
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (z : Fin (m + 1) → ℤ) (v : MaskOriginalDirection m gap t → ℤ × ℤ) : ℝ :=
  MaskOriginalSampling.targetCube gap a C t
    (fun w _ => MaskOriginalSampling.rowMajorant gap C t label w) w (x, z) v

noncomputable def targetMajorantAverage
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) (w : ℕ) : ℝ :=
  expectation (conditionMass (masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val))
    (maskGeneratedCopiedPrimeGood m gap t w)) (fun x =>
      expectation (maskOriginalBaseMass m gap C w) (fun z =>
        expectation (directionPairMass gap t J w x) (targetMajorantCube gap a C t label w x z)))

include ha hC in
theorem profile_target_product_eventually
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ z v u,
      profileProduct gap a C t label (rootMomentTarget d) w x z v u =
        targetMajorantCube gap a C t label w x z v := by
  filter_upwards [MaskOriginalSampling.additiveData_eventually_certificate gap a ha C hC t,
    MaskOriginalSampling.root_target_form_eventually gap a ha C hC t] with w hD hi
  intro x hx z v u
  obtain ⟨H, hdata⟩ := hD x hx
  unfold profileProduct rootMomentTarget
  have hj : Function.Injective (fun η : Fin d → Bool =>
      Fintype.equivFin (RootSmoothedAdditiveCopy d) (rootSmoothedTargetCopy η)) := by
    intro η θ h
    exact rootSmoothedTargetCopy_injective d ((Fintype.equivFin _).injective h)
  rw [Finset.prod_image hj.injOn]
  simp only [rootSmoothedRowEnumeration, Equiv.symm_apply_apply, rootSmoothedTargetCopy,
    rootSmoothedCopy, replicaRootCopy, rootPairValues, Bool.false_eq_true, ite_false]
  unfold targetMajorantCube MaskOriginalSampling.targetCube
  apply Finset.prod_congr rfl
  intro η _
  apply congrArg (MaskOriginalSampling.rowMajorant gap C t label w none)
  let z' : Fin (m + 1) → ℤ := fun col => z col + MaskOriginalSampling.rootShift gap a C t w x u.1 col
  calc
    _ = H.data.translatedForm none η z' (predictionPairValues v) :=
      congrArg (fun D : AdditiveRowData d (m + 1) => D.translatedForm none η z' (predictionPairValues v)) hdata
    _ = H.data.form none z' +
        ((maskGeneratedRowDataFamily m gap t).rows.translationModulus (maskGeneratedMaster m gap) w x
          (maskGeneratedRowDataFamily m gap t).target : ℤ) * ∑ k, predictionPairValues v k (η k) := by
      simp only [AdditiveRowData.translatedForm, H.target_response, Finset.mul_sum]
    _ = _ := congrArg (fun q : ℤ => q +
        ((maskGeneratedRowDataFamily m gap t).rows.translationModulus (maskGeneratedMaster m gap) w x
          (maskGeneratedRowDataFamily m gap t).target : ℤ) * ∑ k, predictionPairValues v k (η k))
      ((H.form_eq none z').trans (hi x hx z u.1))

include ha hC in
theorem profile_target_average_eq_eventually
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, profileAverage gap a C t J label (rootMomentTarget d) w =
      targetMajorantAverage gap a C t J label w := by
  filter_upwards [profile_target_product_eventually gap a ha C hC t label] with w hw
  unfold profileAverage targetMajorantAverage
  apply expectation_congr_support
  intro x hx
  have hxG := conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) x hx
  apply congrArg (expectation (maskOriginalBaseMass m gap C w))
  funext z
  apply congrArg (expectation (directionPairMass gap t J w x))
  funext v
  have he : (fun u₀ => expectation (MaskOriginalSampling.rootMass (m := m) gap w)
      (fun u₁ => profileProduct gap a C t label (rootMomentTarget d) w x z v (u₀, u₁))) =
      (fun _u₀ => targetMajorantCube gap a C t label w x z v) := by
    funext u₀
    have hp : (fun u₁ => profileProduct gap a C t label (rootMomentTarget d) w x z v (u₀, u₁)) =
        (fun _u₁ => targetMajorantCube gap a C t label w x z v) := funext (fun u₁ => hw x hxG z v (u₀, u₁))
    rw [hp, expectation_const, (MaskOriginalSampling.rootMass_probability gap w).2, one_mul]
  rw [he, expectation_const, (MaskOriginalSampling.rootMass_probability gap w).2, one_mul]

include ha hC hJ hgap in
theorem targetMajorantAverage_tendsto
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    Tendsto (targetMajorantAverage gap a C t J label) atTop (𝓝 (((2 ^ (2 ^ d) : ℕ) : ℝ))) := by
  have ht := profileAverage_tendsto gap a ha C hC t J hJ hgap htail label (rootMomentTarget d)
  have hc := congrArg (fun q : ℕ => Tendsto (profileAverage gap a C t J label (rootMomentTarget d))
    atTop (𝓝 (((2 ^ q : ℕ) : ℝ)))) (rootMomentTarget_card d)
  have hp := hc.mp ht
  exact hp.congr' (profile_target_average_eq_eventually gap a ha C hC t J label)

end Hindman168.MaskRootOriginalSampling
