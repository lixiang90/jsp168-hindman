import Hindman168.MaskNativeWeightedReplacement

/-! The native moment mass is the exact original outside-and-completed
pair law. Completion off the good-prime event changes no supported term.
Weighted replacement therefore applies to the actual terminal average. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

local notation "χ" => outsideMass gap a ha C hC t J hJ hgap
local notation "ν" => completedDirectionMass gap a ha C hC t J hJ hgap

theorem original_pair_average_eq_native (w : ℕ)
    (f : MaskOriginalPoint m gap t → (MaskOriginalDirection m gap t → ℤ × ℤ) → ℝ) :
    expectation (χ w) (fun p => expectation (piMass (fun k => tensor (ν w p k) (ν w p k))) (f p)) =
      expectation (MaskRootOriginalSampling.nativeJointMass gap C t J w)
        (fun p => f (p.1, p.2.1) p.2.2) := by
  unfold outsideMass
  rw [expectation_conditionalJoint, MaskRootOriginalSampling.expectation_nativeJointMass]
  apply expectation_congr_support
  intro x hx
  have hxG := conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) x hx
  apply congrArg (expectation (maskOriginalBaseMass m gap C w))
  funext z
  have hd : piMass (fun k => tensor (ν w (x, z) k) (ν w (x, z) k)) =
      MaskRootOriginalSampling.directionPairMass gap t J w x := by
    unfold completedDirectionMass eventCompletedDirectionMass MaskRootOriginalSampling.directionPairMass
    simp only [if_pos hxG]
    rfl
  rw [hd]
  rfl

theorem smoothedTerminalAverage_eq_native
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) :
    smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w =
      expectation (MaskRootOriginalSampling.nativeJointMass gap C t J w) (fun p =>
        MaskRootOriginalSampling.nativeG gap a C t F w p *
          MaskRootOriginalSampling.nativeH gap C t a label w p) := by
  unfold smoothedTerminalAverage
  rw [original_pair_average_eq_native]
  rfl

noncomputable def targetCubeAverage
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) : ℝ :=
  expectation (χ w) (fun p => expectation (piMass (fun k => tensor (ν w p k) (ν w p k)))
    (targetCube gap a C t F w p))

theorem targetCubeAverage_eq_native
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) :
    targetCubeAverage gap a ha C hC t J hJ hgap F w =
      expectation (MaskRootOriginalSampling.nativeJointMass gap C t J w)
        (MaskRootOriginalSampling.nativeG gap a C t F w) := by
  unfold targetCubeAverage
  rw [original_pair_average_eq_native]
  rfl

theorem source_smoothed_replacement_tendsto_zero
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1) :
    Tendsto (fun w => smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w -
      MaskRootOriginalSampling.retainedMeanConstant m gap t *
        targetCubeAverage gap a ha C hC t J hJ hgap F w) atTop (𝓝 0) := by
  have ht := MaskRootOriginalSampling.source_native_terminal_replacement_tendsto_zero
    gap a ha C hC t J hJ hgap htail label F hroot
  exact ht.congr (fun w => by rw [smoothedTerminalAverage_eq_native, targetCubeAverage_eq_native])

end Hindman168.MaskOriginalSampling
