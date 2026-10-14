import Hindman168.MaskTargetAnchorComparison
import Hindman168.MaskGeneralFunctionBounds

/-! General target-row version under |F_root| ≤ 1 + ν.
The original sampling laws and retained majorants remain unchanged.
All error estimates are proved from the source parameters. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

include hC in
theorem source_rootCubeTest_eventually_bounded_majorized
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ rowMajorant gap C t label w none y) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ v y,
      |rootCubeTest gap t F w x v y| ≤ rootCubeBound gap t w := by
  filter_upwards [rowMajorant_eventually_le gap C hC t htail label, hroot] with w hb hr
  intro x hx v y
  let V : ℝ := (maskGeneratedMaster m gap).auxiliary w (gap w).val
  have hf (z : ℤ) : |F w x none z| ≤ V ^ 2 :=
    (hr x hx z).trans (hb none z)
  unfold rootCubeTest rootCubeBound
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _η : MaskOriginalDirection m gap t → Bool, V ^ 2 :=
      Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun _ _ => hf _)
    _ = (V ^ 2) ^ Fintype.card (MaskOriginalDirection m gap t → Bool) := by
      rw [Finset.prod_const, Finset.card_univ]
    _ = _ := by rw [Fintype.card_fun, Fintype.card_bool, ← pow_mul]

include ha hC in
theorem source_targetCube_anchor_comparison_majorized
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ rowMajorant gap C t label w none y) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ rest v,
      |expectation
          (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t))) (primorial w))
          (fun y => targetCube gap a C t F w (x, insertPivotCoordinate (targetRootAnchor gap t) rest y) v) -
        expectation (integerProgressionMass
          ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t))) (primorial w)
          (targetRootMultiplier gap t x) (targetRootOffset gap a C t w x rest v))
          (rootCubeTest gap t F w x v)| ≤
        rootCubeBound gap t w * affineRootError
          ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t))) (primorial w)
          (targetRootMultiplier gap t x) (targetRootOffset gap a C t w x rest v).natAbs := by
  have hM := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [targetRoot_arithmetic_eventually gap a ha C hC t,
    cubeRootValue_affine_eventually gap a ha C hC t,
    targetRootOffset_W_eventually gap a ha C hC t,
    targetRootMultiplier_eventually_le_cutoff gap C hC t hgap,
    source_rootCubeTest_eventually_bounded_majorized gap C hC t htail label F hroot,
    hM.raw_cutoffs_valid] with w haff hv hW hkX hb hvalid
  intro x hx rest v
  have hp := hvalid ((C w).pivot (targetRootAnchor gap t))
    (hC w (targetRootAnchor gap t) (by simp [Chain.block]))
  have heq : (fun y => targetCube gap a C t F w
      (x, insertPivotCoordinate (targetRootAnchor gap t) rest y) v) =
      (fun y => rootCubeTest gap t F w x v
        ((targetRootMultiplier gap t x : ℤ) * y + targetRootOffset gap a C t w x rest v)) := by
    funext y
    exact (targetCube_eq_rootCubeTest gap a C t F w x _ v).trans
      (congrArg (rootCubeTest gap t F w x v) (hv x hx rest v y))
  rw [heq]
  exact integer_harmonic_affine_expectation_error hp.1 (primorial_pos w)
    (haff x hx).1 (hkX x hx _) (haff x hx).2.1 hp.2.1 (hW x hx rest v)
    _ _ (by unfold rootCubeBound; positivity) (hb x hx v)

end Hindman168.MaskOriginalSampling
