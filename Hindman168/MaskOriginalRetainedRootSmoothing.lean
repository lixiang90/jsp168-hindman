import Hindman168.MaskOriginalRootSmoothing
import Hindman168.MaskOriginalInsertionPowers

/-! Root smoothing of the complete actual terminal product G * Psi.
Every retained weight is kept. Its polynomial sup loss is derived from
the source tail masks and canonical copy count, and absorbed by actual
master translation growth. This does not yet replace Psi by its mean. -/

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

def retainedSupExponent (m : ℕ) : ℕ := 2 * ((maskRowCountBound m + 1) * 2 ^ maskRowCountBound m)

include ha hC in
theorem terminal_integrand_flat_eventually
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ z v,
      targetCube gap a C t F w (x, z) v * retainedMajorant gap a C t label w (x, z) v =
        ∏ r : MaskCopiedRow m gap t,
          if r.val.1 = none then
            F w x none ((additiveData gap a C t w x).translatedForm r.val.1 r.val.2 z (predictionPairValues v))
          else rowMajorant gap C t label w r.val.1
            ((additiveData gap a C t w x).translatedForm r.val.1 r.val.2 z (predictionPairValues v)) := by
  filter_upwards [terminal_integrand_actual gap a ha C hC t label F] with w hw
  intro x hx z v
  have hF : completedTest gap t F w (x, z) = F w x := funext (fun _ => funext (fun _ => if_pos hx))
  have hΩ : completedMajorant gap C t label w (x, z) = rowMajorant gap C t label w :=
    funext (fun _ => funext (fun _ => if_pos hx))
  have he := hw x hx z v
  rw [hF, hΩ] at he
  exact he.symm.trans ((additiveData gap a C t w x).eliminationIntegrand_terminal_flat z v _ _)

include ha hC in
theorem terminal_integrand_eventually_bound
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ z v,
      |targetCube gap a C t F w (x, z) v * retainedMajorant gap a C t label w (x, z) v| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ retainedSupExponent m := by
  filter_upwards [terminal_integrand_flat_eventually gap a ha C hC t label F,
    source_tests_eventually_sup_bound gap C hC t htail label F hroot hF,
    rowMajorant_eventually_nonneg gap C hC t label,
    rowMajorant_eventually_le gap C hC t htail label] with w he hf hn hb
  intro x hx z v
  rw [he x hx z v, Finset.abs_prod]
  let V : ℝ := (maskGeneratedMaster m gap).auxiliary w (gap w).val
  have hV : 1 ≤ V := by
    change (1 : ℝ) ≤ (maskGeneratedMaster m gap).auxiliary w (gap w).val
    exact_mod_cast (by decide : 1 ≤ 2).trans ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val)
  calc
    _ ≤ ∏ _r : MaskCopiedRow m gap t, V ^ 2 := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro r _
      split_ifs
      · exact hf x hx none _
      · rw [abs_of_nonneg (hn _ _)]
        exact hb _ _
    _ = V ^ (2 * Fintype.card (MaskCopiedRow m gap t)) := by
      simp only [Finset.prod_const, Finset.card_univ, ← pow_mul]
    _ ≤ _ := pow_le_pow_right₀ hV (Nat.mul_le_mul_left 2 (maskCopiedRow_card_le m gap t))

noncomputable def terminalTest
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) (z : Fin (m + 1) → ℤ) : ℝ :=
  expectation (piMass (fun k => tensor (ν w (x, fun _ => 0) k) (ν w (x, fun _ => 0) k)))
    (fun v => targetCube gap a C t F w (x, z) v * retainedMajorant gap a C t label w (x, z) v)

theorem terminalTest_average_eq
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) :
    originalTestAverage gap a ha C hC t J hJ hgap
      (terminalTest gap a ha C hC t J hJ hgap label F) w =
        terminalAverage gap a ha C hC t J hJ hgap label F w := rfl

theorem terminalTest_eventually_bound
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ z,
      |terminalTest gap a ha C hC t J hJ hgap label F w x z| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ retainedSupExponent m := by
  filter_upwards [terminal_integrand_eventually_bound gap a ha C hC t htail label F hroot hF,
    completed_direction_probability_eventually gap a ha C hC t J hJ hgap] with w hb hd
  intro x hx z
  unfold terminalTest
  apply expectation_probability_support_bound
  · exact piMass_nonneg _ (fun k => tensor_nonneg _ _
      (hd.1 (x, fun _ => 0) k) (hd.1 (x, fun _ => 0) k))
  · apply piMass_total_one
    intro k
    rw [tensor_total, hd.2 (x, fun _ => 0) k, one_mul]
  · exact fun v _ => hb x hx z v

theorem source_terminal_root_smoothing_rapid
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
      (fun w => rootSmoothedAverage gap a ha C hC t J hJ hgap
        (terminalTest gap a ha C hC t J hJ hgap label F) w -
          terminalAverage gap a ha C hC t J hJ hgap label F w) := by
  simpa only [terminalTest_average_eq] using root_smoothing_difference_rapid gap a ha C hC t J hJ hgap
    (terminalTest gap a ha C hC t J hJ hgap label F) (retainedSupExponent m)
    (terminalTest_eventually_bound gap a ha C hC t J hJ hgap htail label F hroot hF)

end Hindman168.MaskOriginalSampling
