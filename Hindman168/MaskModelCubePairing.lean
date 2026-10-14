import Hindman168.FiniteSupportedConditioning
import Hindman168.SingleRepeatedDualCube
import Hindman168.MaskEndpointTargetCube

/-! The actual mask endpoint cube is exactly a pairing with its generated
original row-template dual test. Both conditional prime laws, every
polynomial modulus, every quotient interval and the harmonic root remain
unchanged. The equality holds at every parameter, even for zero event mass. -/

set_option maxHeartbeats 2000000

namespace Hindman168
open scoped BigOperators Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m+1))
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ)

theorem maskTargetPredictionOrder_eq_template :
    targetPredictionOrder gap t = (maskGeneratedRowDataFamily m gap t).template.dimension := by
  exact PolynomialRowFamily.offTargetRow_card _

theorem maskRootPrimeMass_eq_original_dual (w : ℕ) :
    rootPrimeMass gap t w = conditionMass
      (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
        ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper)
      (predictionLocalPrimeGoodEvent (maskGeneratedMaster m gap)
        ((maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target)
        ((maskGeneratedRowDataFamily m gap t).rows.denominator (maskGeneratedRowDataFamily m gap t).target) w) := by
  exact conditionMass_support_restriction _ _

theorem maskEndpointTargetCube_eq_repeated_prediction_dual (w : ℕ) (g : ℤ → ℝ) :
    maskEndpointTargetCube gap C t J w g =
      expectation (integerMass ((maskGeneratedMaster m gap).cutoff w
        ((C w).pivot (targetRootAnchor gap t))) (primorial w)) (fun y => g y *
        masterSingleGoodDualTest (maskGeneratedMaster m gap) (targetPredictionOrder gap t) gap
          (fun _ : Fin 1 => J) (fun _ => 0)
          ((maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target)
          ((maskGeneratedRowDataFamily m gap t).rows.denominator (maskGeneratedRowDataFamily m gap t).target)
          (fun _ _ => 1) (fun _ _ _ => g) w y) := by
  unfold maskEndpointTargetCube targetUnrestrictedAverage rootCubeTest MaskRootOriginalSampling.directionPairMass
  rw [prediction_repeated_dual_cube]
  rw [maskRootPrimeMass_eq_original_dual]
  unfold masterSingleGoodDualTest
  simp only [PolynomialRowFamily.translationModulus, predictionCubeModulus, Int.natCast_mul]
  rfl

noncomputable def maskTargetRepeatedDualInput (g : ℤ → ℝ) :
    OriginalSingleDualInput (maskGeneratedRowDataFamily m gap t).arity
      (maskGeneratedRowDataFamily m gap t).template.dimension :=
  originalRepeatedDualInput _ _ g

theorem maskEndpointTargetCube_eq_original_template_pairing (w : ℕ) (g : ℤ → ℝ) :
    maskEndpointTargetCube gap C t J w g =
      expectation (integerMass ((maskGeneratedMaster m gap).cutoff w
        ((C w).pivot (targetRootAnchor gap t))) (primorial w)) (fun y => g y *
        (maskGeneratedRowDataFamily m gap t).template.dual (maskGeneratedMaster m gap)
          (fun _ => J) (maskTargetRepeatedDualInput gap t g) w y) := by
  simp only [maskTargetRepeatedDualInput, OriginalDualTemplate.dual,
    OriginalPolynomialRowData.template, originalRepeatedDualInput]
  have hd : targetPredictionOrder gap t = (maskGeneratedRowDataFamily m gap t).rowCount - 1 :=
    maskTargetPredictionOrder_eq_template gap t
  rw [← hd]
  exact maskEndpointTargetCube_eq_repeated_prediction_dual gap C t J w g

theorem maskTargetRepeatedDualInput_admissible (label : ℕ → Fin (m+1)) (w : ℕ)
    (g : ℤ → ℝ) (hg : ∀ y, |g y| ≤ 1 + masterPredictionBlockMask (maskGeneratedMaster m gap) C label w y) :
    (maskTargetRepeatedDualInput gap t g).Admissible (maskGeneratedMaster m gap) C label w :=
  originalRepeatedDualInput_admissible _ C label w g hg

end Hindman168
