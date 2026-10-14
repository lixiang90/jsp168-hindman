import Hindman168.MaskOriginalRetainedRootSmoothing

/-! Exact root-smoothed terminal expression G * E_root Psi, and the
original unshifted recurrence with a proved vanishing error. The retained
factor is still present; the three mixed moment limits remain separate. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

local notation "S" => maskOriginalSampling m gap a ha C hC t J hJ hgap
local notation "χ" => outsideMass gap a ha C hC t J hJ hgap
local notation "ν" => completedDirectionMass gap a ha C hC t J hJ hgap

noncomputable def smoothedRetainedMajorant
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) (p : MaskOriginalPoint m gap t) (v : MaskOriginalDirection m gap t → ℤ × ℤ) : ℝ :=
  expectation (rootMass (m := m) gap w) (fun u₀ => retainedMajorant gap a C t label w
    (p.1, fun col => p.2 col + rootShift gap a C t w p.1 u₀ col) v)

noncomputable def smoothedTerminalAverage
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) : ℝ :=
  expectation (χ w) (fun p => expectation (piMass (fun k => tensor (ν w p k) (ν w p k)))
    (fun v => targetCube gap a C t F w p v * smoothedRetainedMajorant gap a C t label w p v))

include hC in
theorem smoothedRetainedMajorant_eventually_nonneg
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, ∀ p v, 0 ≤ smoothedRetainedMajorant gap a C t label w p v := by
  filter_upwards [retainedMajorant_eventually_nonneg gap a C hC t label] with w hw
  intro p v
  exact expectation_nonneg _ _ (rootMass_probability gap w).1 (fun _ => hw _ v)

theorem rootSmoothedAverage_terminal_eq_eventually
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ) :
    ∀ᶠ w in atTop,
      rootSmoothedAverage gap a ha C hC t J hJ hgap
        (terminalTest gap a ha C hC t J hJ hgap label F) w =
          smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w := by
  filter_upwards [targetCube_root_shift_eventually gap a ha C hC t F] with w hi
  rw [rootSmoothedAverage_eq_shift gap a ha C hC t J hJ hgap]
  unfold smoothedTerminalAverage outsideMass
  rw [expectation_conditionalJoint]
  apply expectation_congr_support
  intro x hx
  have hxG := conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) x hx
  rw [expectation_comm (rootMass (m := m) gap w) (maskOriginalBaseMass m gap C w)]
  apply congrArg (expectation (maskOriginalBaseMass m gap C w))
  funext z
  unfold terminalTest
  rw [expectation_comm]
  apply congrArg (expectation (piMass (fun k => tensor (ν w (x, fun _ => 0) k) (ν w (x, fun _ => 0) k))))
  funext v
  unfold smoothedRetainedMajorant
  calc
    _ = expectation (rootMass (m := m) gap w) (fun u₀ => targetCube gap a C t F w (x, z) v *
        retainedMajorant gap a C t label w (x, fun col => z col + rootShift gap a C t w x u₀ col) v) := by
      apply congrArg (expectation (rootMass (m := m) gap w))
      funext u₀
      rw [hi x hxG z v u₀]
    _ = _ := expectation_const_mul _ _ _

theorem source_smoothed_terminal_difference_rapid
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) :
    RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (fun w => smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w -
        terminalAverage gap a ha C hC t J hJ hgap label F w) := by
  apply (source_terminal_root_smoothing_rapid gap a ha C hC t J hJ hgap htail label F hroot hF).of_abs_le
  filter_upwards [rootSmoothedAverage_terminal_eq_eventually gap a ha C hC t J hJ hgap label F] with w hw
  rw [hw]

theorem source_smoothed_terminal_weighted_tendsto
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) (q : ℕ) :
    Tendsto (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q *
      |smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w -
        terminalAverage gap a ha C hC t J hJ hgap label F w|) atTop (𝓝 0) := by
  have ht : Tendsto (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q *
      (smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w -
        terminalAverage gap a ha C hC t J hJ hgap label F w)) atTop (𝓝 0) := by
    apply (Asymptotics.isLittleO_one_iff ℝ).mp
    simpa only [pow_zero, inv_one] using
      ((source_smoothed_terminal_difference_rapid gap a ha C hC t J hJ hgap htail label F hroot hF).mul_power
        (Eventually.of_forall (fun w => by
          exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
            ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val))) q) 0
  have hv (w : ℕ) : |((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q| =
      ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q :=
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) q)
  simpa only [abs_zero, abs_mul, hv] using ht.abs

theorem source_unshifted_smoothed_recurrence
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ w in atTop,
      |unshiftedCorrelation gap a ha C hC t J hJ hgap F w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) ≤
      maskAdditiveRecurrenceBound m * |smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w| + e w := by
  obtain ⟨e, he, hb⟩ := source_unshifted_recurrence gap a ha C hC t J hJ hgap htail label F hroot hF
  let δ : ℕ → ℝ := fun w => |smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w -
    terminalAverage gap a ha C hC t J hJ hgap label F w|
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using source_smoothed_terminal_weighted_tendsto
      gap a ha C hC t J hJ hgap htail label F hroot hF 0
  refine ⟨fun w => e w + maskAdditiveRecurrenceBound m * δ w, ?_, ?_⟩
  · simpa only [mul_zero, add_zero] using he.add (hδ.const_mul (maskAdditiveRecurrenceBound m))
  · filter_upwards [hb] with w hw
    have hD : 0 ≤ maskAdditiveRecurrenceBound m := le_trans (by norm_num)
      (maskAdditiveRecurrenceBound_ge_one m)
    have hd := abs_abs_sub_abs_le_abs_sub
      (smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w)
      (terminalAverage gap a ha C hC t J hJ hgap label F w)
    have hh := neg_le_of_abs_le hd
    have hnorm : |terminalAverage gap a ha C hC t J hJ hgap label F w| ≤
        |smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w| + δ w := by
      dsimp only [δ]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hnorm hD
    linarith

end Hindman168.MaskOriginalSampling
