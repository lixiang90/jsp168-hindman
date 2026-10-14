import Hindman168.MaskTargetSecondCoordinate
import Hindman168.HarmonicLinearProgressionAverage

/-! Remove the actual anchor congruence restriction by averaging the second
supported harmonic coordinate. The prime tuple, smooth column coefficients,
remaining product law and original cube test are all retained. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def targetRootOtherIndex :
    {col : Fin (m + 1) // col ≠ targetRootAnchor gap t} :=
  ⟨targetRootOtherColumn gap t, ne_of_lt (targetRootOtherColumn_properties gap t).1⟩

theorem targetRootOtherIndex_val : (targetRootOtherIndex gap t).val = targetRootOtherColumn gap t := rfl

include ha hC in
theorem source_targetRootRest_progression_error
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ v,
      |expectation (rootRestMass gap C t w) (fun rest =>
          expectation (integerProgressionMass
            ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t))) (primorial w)
            (targetRootMultiplier gap t x) (targetRootOffset gap a C t w x rest v))
            (rootCubeTest gap t F w x v)) -
        expectation (integerMass
          ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t))) (primorial w))
          (rootCubeTest gap t F w x v)| ≤
        (targetRootMultiplier gap t x : ℝ) * rootCubeBound gap t w * residueError
          ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootOtherColumn gap t)))
          (primorial w) (targetRootMultiplier gap t x) := by
  have hM := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [actual_target_second_coordinate_unit gap a ha C hC t,
    targetRoot_arithmetic_eventually gap a ha C hC t,
    base_coordinates_probability_eventually gap C hC,
    source_rootCubeTest_eventually_bounded gap C hC t htail label F hroot,
    hM.raw_cutoffs_valid] with w hu hk hp hb hv
  intro x hx v
  let k := targetRootMultiplier gap t x
  letI : NeZero k := ⟨Nat.ne_of_gt (hk x hx).1⟩
  let ν := fun col : {col : Fin (m + 1) // col ≠ targetRootAnchor gap t} =>
    integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col.val)) (primorial w)
  let c := fun col : {col : Fin (m + 1) // col ≠ targetRootAnchor gap t} =>
    (maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerRow x
      (masterColumnCoefficient N a (fun w => (C w).block) w)
      (maskGeneratedRowDataFamily m gap t).target col.val
  let h : ℤ := ((maskGeneratedRowDataFamily m gap t).rows.translationModulus
    (maskGeneratedMaster m gap) w x (maskGeneratedRowDataFamily m gap t).target : ℤ) * ∑ d, (v d).1
  let μ := integerMass
    ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t))) (primorial w)
  have hvalid := hv ((C w).pivot (targetRootOtherColumn gap t))
    (hC w (targetRootOtherColumn gap t) (by simp [Chain.block]))
  change |expectation (piMass ν) (fun rest =>
      expectation (integerProgressionMass
        ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t)))
        (primorial w) k ((∑ col, c col * rest col) + h)) (rootCubeTest gap t F w x v)) -
      expectation μ (rootCubeTest gap t F w x v)| ≤ _
  simp_rw [integerProgressionMass_eq_residueClass]
  exact harmonic_linear_progression_average_error ν
    (fun col => (hp col.val).1) (fun col => (hp col.val).2)
    (targetRootOtherIndex gap t) rfl c h μ (hp _).1 (hp _).2
    hvalid.1 (primorial_pos w) (hk x hx).2.1 hvalid.2.1 (hu x hx)
    (rootCubeTest gap t F w x v) (rootCubeBound gap t w)
    (by unfold rootCubeBound; positivity) (hb x hx v)

end Hindman168.MaskOriginalSampling
