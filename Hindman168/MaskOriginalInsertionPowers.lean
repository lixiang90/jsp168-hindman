import Hindman168.MaskOriginalInsertionLimit
import Mathlib.Algebra.Order.Ring.Abs

/-! Initial insertion remains negligible after the actual finite recurrence
power. The original unshifted source correlation therefore obeys the
m-only recurrence with an explicit vanishing error and the full retained
majorant product. Retained-weight removal is not performed here. -/

set_option maxHeartbeats 2000000

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem expectation_probability_support_bound {α : Type*}
    (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x) (ht : total μ = 1) (f : α → ℝ) (B : ℝ)
    (hf : ∀ x ∈ μ.support, |f x| ≤ B) : |expectation μ f| ≤ B := by
  have he := expectation_difference_support_bound μ hμ f (fun _ => 0) B
    (fun x hx => by simpa only [sub_zero] using hf x hx)
  simpa only [expectation_const, ht, mul_zero, sub_zero, one_mul] using he

end Hindman168.FiniteMass

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

theorem RapidlySmall.abs_power_difference {α : Type*} {l : Filter α} {V f g : α → ℝ}
    (he : RapidlySmall l V (fun w => f w - g w))
    (hV : ∀ᶠ w in l, 0 < V w) (K p : ℕ)
    (hf : ∀ᶠ w in l, |f w| ≤ V w ^ K) (hg : ∀ᶠ w in l, |g w| ≤ V w ^ K) :
    RapidlySmall l V (fun w => |f w| ^ p - |g w| ^ p) := by
  apply ((he.mul_power hV (K * (p - 1))).const_mul (p : ℝ)).of_abs_le
  filter_upwards [hf, hg, hV] with w hfw hgw hVw
  have hm : 0 ≤ max |f w| |g w| := (abs_nonneg _).trans (le_max_left _ _)
  have hp := pow_le_pow_left₀ hm (max_le hfw hgw) (p - 1)
  have ha := abs_pow_sub_pow_le (a := |f w|) (b := |g w|) (n := p)
  simp only [abs_abs] at ha
  calc
    _ ≤ abs (|f w| - |g w|) * (p : ℝ) * max |f w| |g w| ^ (p - 1) := ha
    _ ≤ |f w - g w| * (p : ℝ) * (V w ^ K) ^ (p - 1) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right (abs_abs_sub_abs_le_abs_sub _ _) (Nat.cast_nonneg p)) hp
        (pow_nonneg hm _) (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg p))
    _ = |(p : ℝ) * (V w ^ (K * (p - 1)) * (f w - g w))| := by
      simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (p : ℝ) from Nat.cast_nonneg p), pow_mul]
      rw [abs_of_nonneg (pow_nonneg (pow_nonneg hVw.le K) (p - 1))]
      ring

end Hindman168

namespace Hindman168.MaskOriginalSampling

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

local notation "S" => maskOriginalSampling m gap a ha C hC t J hJ hgap
local notation "ν" => completedDirectionMass gap a ha C hC t J hJ hgap

theorem correlations_eventually_bounded
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (B : ℕ)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ base y,
      |F w x base y| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B) :
    ∀ᶠ w in atTop,
      |unshiftedCorrelation gap a ha C hC t J hJ hgap F w| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^
          (B * Fintype.card (MaskOriginalBaseRow m gap t)) ∧
      |insertedCorrelation gap a ha C hC t J hJ hgap F w| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^
          (B * Fintype.card (MaskOriginalBaseRow m gap t)) := by
  filter_upwards [(S).conditioned_prime_probability_eventually,
    base_probability_eventually gap C hC,
    completed_direction_probability_eventually gap a ha C hC t J hJ hgap, hF] with w hp hb hd hf
  have ht : total (conditionMass ((S).primeMass w) (maskGeneratedCopiedPrimeGood m gap t w)) = 1 := hp.2
  rw [insertedCorrelation_eq_shift gap a ha C hC t J hJ hgap F w]
  unfold unshiftedCorrelation outsideMass
  rw [expectation_conditionalJoint]
  constructor
  · apply expectation_probability_support_bound _ hp.1 ht
    intro x hx
    have hxG := conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) x hx
    apply expectation_probability_support_bound _ hb.1 hb.2
    intro z _
    exact originalProduct_bound gap a C t F w x B (hf x hxG) z
  · apply expectation_probability_support_bound _ hp.1 ht
    intro x hx
    have hxG := conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) x hx
    apply expectation_probability_support_bound _ (piMass_nonneg _ (hd.1 (x, fun _ => 0)))
      (piMass_total_one _ (hd.2 (x, fun _ => 0)))
    intro u _
    apply expectation_probability_support_bound _ hb.1 hb.2
    intro z _
    exact originalProduct_bound gap a C t F w x B (hf x hxG) _

noncomputable def insertionPowerError
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) : ℝ :=
  |unshiftedCorrelation gap a ha C hC t J hJ hgap F w| ^
      (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) -
    |insertedCorrelation gap a ha C hC t J hJ hgap F w| ^
      (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target))

theorem source_insertion_power_error_rapid
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
      (insertionPowerError gap a ha C hC t J hJ hgap F) := by
  have hi := source_insertion_difference_rapid gap a ha C hC t J hJ hgap htail label F hroot hF
  have he : RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (fun w => unshiftedCorrelation gap a ha C hC t J hJ hgap F w -
        insertedCorrelation gap a ha C hC t J hJ hgap F w) :=
    hi.of_abs_le (Eventually.of_forall (fun w => le_of_eq (abs_sub_comm _ _)))
  have hb := correlations_eventually_bounded gap a ha C hC t J hJ hgap F 2
    (source_tests_eventually_sup_bound gap C hC t htail label F hroot hF)
  exact he.abs_power_difference (Eventually.of_forall (fun w => by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
      ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val)))
    (2 * Fintype.card (MaskOriginalBaseRow m gap t))
    (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target))
    (hb.mono (fun _ hw => hw.1)) (hb.mono (fun _ hw => hw.2))

theorem source_insertion_power_error_weighted_tendsto
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
      |insertionPowerError gap a ha C hC t J hJ hgap F w|) atTop (𝓝 0) := by
  have he := source_insertion_power_error_rapid gap a ha C hC t J hJ hgap htail label F hroot hF
  have ht : Tendsto (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q *
      insertionPowerError gap a ha C hC t J hJ hgap F w) atTop (𝓝 0) := by
    apply (Asymptotics.isLittleO_one_iff ℝ).mp
    simpa only [pow_zero, inv_one] using
      (he.mul_power (Eventually.of_forall (fun w => by
        exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
          ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val))) q) 0
  have hv (w : ℕ) :
      |((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q| =
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q :=
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) q)
  simpa only [abs_zero, abs_mul, hv] using ht.abs

theorem source_unshifted_recurrence
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
      maskAdditiveRecurrenceBound m * |terminalAverage gap a ha C hC t J hJ hgap label F w| + e w := by
  refine ⟨fun w => |insertionPowerError gap a ha C hC t J hJ hgap F w|, ?_, ?_⟩
  · simpa only [pow_zero, one_mul] using
      source_insertion_power_error_weighted_tendsto gap a ha C hC t J hJ hgap htail label F hroot hF 0
  · filter_upwards [inserted_correlation_power_bound gap a ha C hC t J hJ hgap htail label F hF] with w hw
    have he := le_abs_self (insertionPowerError gap a ha C hC t J hJ hgap F w)
    change |unshiftedCorrelation gap a ha C hC t J hJ hgap F w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) -
      |insertedCorrelation gap a ha C hC t J hJ hgap F w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) ≤
      |insertionPowerError gap a ha C hC t J hJ hgap F w| at he
    linarith

end Hindman168.MaskOriginalSampling
