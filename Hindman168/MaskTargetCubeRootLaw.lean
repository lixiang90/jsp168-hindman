import Hindman168.MaskOriginalWeightedReplacement
import Hindman168.FinitePivotCoordinates

/-! Exact rebasing of the actual target cube. The root law is the pushforward
of the original harmonic base law; no distributional comparison is assumed. -/

namespace Hindman168.MaskOriginalSampling

open scoped BigOperators Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ)
  (C : ℕ → Chain (m + 1)) (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def cubeRootValue (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (z : Fin (m + 1) → ℤ) (v : MaskOriginalDirection m gap t → ℤ × ℤ) : ℤ :=
  (maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerLinearForm x
    (masterColumnCoefficient N a (fun w => (C w).block) w)
    (maskGeneratedRowDataFamily m gap t).target z +
    ((maskGeneratedRowDataFamily m gap t).rows.translationModulus (maskGeneratedMaster m gap) w x
      (maskGeneratedRowDataFamily m gap t).target : ℤ) * ∑ k, (v k).1

noncomputable def rootCubeTest
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (v : MaskOriginalDirection m gap t → ℤ × ℤ) (y : ℤ) : ℝ :=
  ∏ η : MaskOriginalDirection m gap t → Bool, F w x none (y +
    ((maskGeneratedRowDataFamily m gap t).rows.translationModulus (maskGeneratedMaster m gap) w x
      (maskGeneratedRowDataFamily m gap t).target : ℤ) *
      ∑ k, if η k then (v k).2 - (v k).1 else 0)

noncomputable def cubeRootMass (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (v : MaskOriginalDirection m gap t → ℤ × ℤ) : Mass ℤ :=
  (maskOriginalBaseMass m gap C w).mapDomain (fun z => cubeRootValue gap a C t w x z v)

theorem predictionPairValues_sum_rebase {d : ℕ} (v : Fin d → ℤ × ℤ) (η : Fin d → Bool) :
    (∑ k, predictionPairValues v k (η k)) =
      (∑ k, (v k).1) + ∑ k, if η k then (v k).2 - (v k).1 else 0 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  cases η k <;> simp [predictionPairValues]

theorem targetCube_eq_rootCubeTest
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (z : Fin (m + 1) → ℤ) (v : MaskOriginalDirection m gap t → ℤ × ℤ) :
    targetCube gap a C t F w (x, z) v =
      rootCubeTest gap t F w x v (cubeRootValue gap a C t w x z v) := by
  unfold targetCube rootCubeTest cubeRootValue
  apply Fintype.prod_congr
  intro η
  congr 1
  rw [predictionPairValues_sum_rebase, mul_add, add_assoc]

theorem targetCube_base_expectation_eq_root
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (v : MaskOriginalDirection m gap t → ℤ × ℤ) :
    expectation (maskOriginalBaseMass m gap C w) (fun z => targetCube gap a C t F w (x, z) v) =
      expectation (cubeRootMass gap a C t w x v) (rootCubeTest gap t F w x v) := by
  rw [cubeRootMass, expectation_push]
  apply congrArg (expectation (maskOriginalBaseMass m gap C w))
  funext z
  exact targetCube_eq_rootCubeTest gap a C t F w x z v

end Hindman168.MaskOriginalSampling
