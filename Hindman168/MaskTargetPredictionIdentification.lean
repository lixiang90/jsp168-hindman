import Hindman168.MaskTargetPredictionLimit

/-! Identify the actual conditioned unrestricted cube with the original
prediction average divided by its actual good-event mass. The equality
is exact, including zero denominators, and preserves prime-dependent
quotient interval lengths. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ)

noncomputable def targetCenteredUnrestrictedAverage
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) : ℕ → ℝ :=
  targetUnrestrictedAverage gap C t J (fun w _ _ => targetRootCenteredMask gap C t label w)

theorem targetCenteredUnrestrictedAverage_eq_prediction_normalized
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) (w : ℕ) :
    targetCenteredUnrestrictedAverage gap C t J label w =
      targetPredictionAverage gap C hC t J label w /
        event (masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val))
          (maskGeneratedCopiedPrimeGood m gap t w) := by
  unfold targetCenteredUnrestrictedAverage targetUnrestrictedAverage rootPrimeMass
  rw [expectation_conditionMass]
  unfold targetPredictionAverage masterPredictionOriginalCubeAverage
  apply congrArg (fun e : ℝ => e /
    event (masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val))
      (maskGeneratedCopiedPrimeGood m gap t w))
  apply congrArg (expectation (masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val)))
  funext x
  split_ifs
  · have hT : predictionQuotientLength (maskGeneratedMaster m gap)
        (fun (w : ℕ) (_ : Fin 1) => gap w) J
        (fun (w : ℕ) (_ : Fin 1) => ((maskGeneratedMaster m gap).modulus w : ℕ))
        (fun _ : Fin 1 => targetPredictionPolynomial gap t) w x =
        (fun _ : Fin 1 => maskGeneratedShiftLength m gap t J w x) := by
      funext q
      exact targetPredictionQuotientLength_eq_actual gap t J w x q
    rw [hT]
    simp_rw [targetPredictionModulus_eq_actual]
    rw [singleCube_product_expectation]
    rfl
  · rfl

theorem source_targetUnrestrictedAverage_eq_centered
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1) :
    ∀ᶠ w in atTop, targetUnrestrictedAverage gap C t J F w =
      targetCenteredUnrestrictedAverage gap C t J label w := by
  filter_upwards [hroot] with w hw
  unfold targetUnrestrictedAverage targetCenteredUnrestrictedAverage
  apply expectation_congr_support
  intro x hx
  have he : F w x none = targetRootCenteredMask gap C t label w :=
    hw x (conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) x hx)
  apply congrArg (expectation (MaskRootOriginalSampling.directionPairMass gap t J w x))
  funext v
  apply congrArg (expectation (integerMass
    ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t))) (primorial w)))
  funext y
  unfold rootCubeTest
  simp_rw [he]

end Hindman168.MaskOriginalSampling
