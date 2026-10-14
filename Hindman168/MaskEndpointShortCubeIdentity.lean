import Hindman168.IntegerShortCubeSamplingIdentity
import Hindman168.MaskModelCubePairing
import Hindman168.MaskTargetPredictionData

/-! The actual endpoint target cube uses exactly the original harmonic
short-cube statistic and the retained local prime event. These are exact
identities at every stage, with no positivity or limit hypotheses. -/

namespace Hindman168
open FiniteMass MaskOriginalSampling
open scoped BigOperators Classical

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m+1))
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ)

theorem maskEndpointTargetCube_eq_integer_shortCube (w : ℕ) (g : ℤ → ℝ) :
    maskEndpointTargetCube gap C t J w g =
      expectation (rootPrimeMass gap t w) (fun x =>
        integerPredictionShortCubeStatistic w ((maskGeneratedMaster m gap).modulus w : ℕ)
          ((maskGeneratedMaster m gap).gap w (gap w).val)
          ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t)))
          (targetPredictionOrder gap t) J (targetPredictionPolynomial gap t) g x) := by
  unfold maskEndpointTargetCube targetUnrestrictedAverage
  apply congrArg (expectation (rootPrimeMass gap t w))
  funext x
  rw [integerPredictionShortCubeStatistic_pair_law, targetPredictionModulus_eq_actual,
    Int.natAbs_natCast]
  unfold MaskRootOriginalSampling.directionPairMass maskGeneratedShiftLength rootCubeTest
  simp only [Nat.div_div_eq_div_mul, Nat.mul_comm]
  rfl

theorem maskEndpointTargetCube_eq_local_conditioned_shortCube (w : ℕ) (g : ℤ → ℝ) :
    maskEndpointTargetCube gap C t J w g =
      expectation (conditionMass
        (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
          ((maskGeneratedMaster m gap).pool w (gap w).val).lower
          ((maskGeneratedMaster m gap).pool w (gap w).val).upper)
        (predictionLocalPrimeGoodEvent (maskGeneratedMaster m gap)
          ((maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target)
          (targetPredictionPolynomial gap t) w)) (fun x =>
        integerPredictionShortCubeStatistic w ((maskGeneratedMaster m gap).modulus w : ℕ)
          ((maskGeneratedMaster m gap).gap w (gap w).val)
          ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t)))
          (targetPredictionOrder gap t) J (targetPredictionPolynomial gap t) g x) := by
  rw [maskEndpointTargetCube_eq_integer_shortCube, maskRootPrimeMass_eq_original_dual]
  rfl

theorem maskEndpointTargetCube_abs_le_integer_shortCube (w : ℕ) (g : ℤ → ℝ) :
    |maskEndpointTargetCube gap C t J w g| ≤
      expectation (rootPrimeMass gap t w) (fun x =>
        |integerPredictionShortCubeStatistic w ((maskGeneratedMaster m gap).modulus w : ℕ)
          ((maskGeneratedMaster m gap).gap w (gap w).val)
          ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t)))
          (targetPredictionOrder gap t) J (targetPredictionPolynomial gap t) g x|) := by
  rw [maskEndpointTargetCube_eq_integer_shortCube]
  apply abs_expectation_le_majorant
  · rw [maskRootPrimeMass_eq_original_dual]
    exact conditionMass_nonneg _ _ (primeIndependentMass_nonneg _ _ _)
  · intro x
    exact le_rfl

end Hindman168
