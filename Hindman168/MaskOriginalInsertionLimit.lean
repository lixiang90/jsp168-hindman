import Hindman168.MaskOriginalFunctionBounds

/-! The original unshifted correlation and the actual inserted correlation
are compared under their unchanged normalized joint law. The source tail
majorants and centered root supply the polynomial loss; actual translation
sampling supplies the rapidly-small error. -/

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

noncomputable def originalProduct
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) (z : Fin (m + 1) → ℤ) : ℝ :=
  ∏ i : MaskOriginalBaseRow m gap t, F w x i
    ((maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerLinearForm x
      (masterColumnCoefficient N a (fun w => (C w).block) w)
      (PolynomialRowFamily.additiveIndexEquiv (maskGeneratedRowDataFamily m gap t).target i) z)

noncomputable def unshiftedCorrelation
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) : ℝ := expectation (χ w) (fun p => originalProduct gap a C t F w p.1 p.2)

theorem originalProduct_bound
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) (B : ℕ)
    (hF : ∀ base y, |F w x base y| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B)
    (z : Fin (m + 1) → ℤ) :
    |originalProduct gap a C t F w x z| ≤
      ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (B * Fintype.card (MaskOriginalBaseRow m gap t)) := by
  unfold originalProduct
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _base : MaskOriginalBaseRow m gap t,
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B :=
      Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hF i _)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, ← pow_mul]

theorem insertedCorrelation_eq_shift
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) :
    insertedCorrelation gap a ha C hC t J hJ hgap F w =
      expectation (conditionMass ((S).primeMass w) (maskGeneratedCopiedPrimeGood m gap t w))
        (fun x => expectation (piMass (ν w (x, fun _ => 0))) (fun u =>
          expectation (maskOriginalBaseMass m gap C w) (fun z =>
            originalProduct gap a C t F w x (fun col => z col + insertionShift gap a C t w x u col)))) := by
  change expectation (χ w) (fun p => expectation (piMass (ν w p)) (fun u =>
    originalProduct gap a C t F w p.1 (fun col => p.2 col + insertionShift gap a C t w p.1 u col))) = _
  unfold outsideMass
  rw [expectation_conditionalJoint]
  apply congrArg (expectation (conditionMass ((S).primeMass w) (maskGeneratedCopiedPrimeGood m gap t w)))
  funext x
  change expectation (maskOriginalBaseMass m gap C w) (fun z =>
    expectation (piMass (ν w (x, fun _ => 0))) (fun u =>
      originalProduct gap a C t F w x (fun col => z col + insertionShift gap a C t w x u col))) = _
  exact expectation_comm _ _ _

theorem insertion_difference_eventually_bound
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (B : ℕ)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ base y,
      |F w x base y| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B) :
    ∀ᶠ w in atTop,
      |insertedCorrelation gap a ha C hC t J hJ hgap F w -
        unshiftedCorrelation gap a ha C hC t J hJ hgap F w| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^
          (B * Fintype.card (MaskOriginalBaseRow m gap t)) * insertionErrorCap gap C w := by
  filter_upwards [(S).conditioned_prime_probability_eventually,
    base_coordinates_probability_eventually gap C hC,
    completed_direction_probability_eventually gap a ha C hC t J hJ hgap,
    insertionShift_distance_eventually gap a ha C hC t J hJ hgap, hF] with w hp hc hd hδ hf
  rw [insertedCorrelation_eq_shift gap a ha C hC t J hJ hgap F w]
  unfold unshiftedCorrelation outsideMass
  rw [expectation_conditionalJoint]
  have he := expectation_difference_support_bound
    (conditionMass ((S).primeMass w) (maskGeneratedCopiedPrimeGood m gap t w)) hp.1
    (fun x => expectation (piMass (ν w (x, fun _ => 0))) (fun u =>
      expectation (maskOriginalBaseMass m gap C w) (fun z =>
        originalProduct gap a C t F w x (fun col => z col + insertionShift gap a C t w x u col))))
    (fun x => expectation (maskOriginalBaseMass m gap C w) (originalProduct gap a C t F w x))
    (((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^
      (B * Fintype.card (MaskOriginalBaseRow m gap t)) * insertionErrorCap gap C w) (by
      intro x hx
      have hxG := conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) x hx
      exact averaged_piMass_translation_expectation_bound
        (fun col : Fin (m + 1) => integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
        (piMass (ν w (x, fun _ => 0))) (insertionShift gap a C t w x)
        (originalProduct gap a C t F w x)
        (fun col => (hc col).1) (fun col => (hc col).2)
        (piMass_nonneg _ (hd.1 (x, fun _ => 0)))
        (piMass_total_one _ (hd.2 (x, fun _ => 0)))
        (by positivity) (originalProduct_bound gap a C t F w x B (hf x hxG))
        (fun u hu => hδ x hxG (fun _ => 0) u hu))
  have ht : total (conditionMass ((S).primeMass w) (maskGeneratedCopiedPrimeGood m gap t w)) = 1 := hp.2
  have hs := congrArg (fun r : ℝ => r *
    (((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^
      (B * Fintype.card (MaskOriginalBaseRow m gap t)) * insertionErrorCap gap C w)) ht
  exact he.trans (le_of_eq (hs.trans (one_mul _)))

theorem insertion_difference_rapid
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (B : ℕ)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ base y,
      |F w x base y| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B) :
    RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (fun w => insertedCorrelation gap a ha C hC t J hJ hgap F w -
        unshiftedCorrelation gap a ha C hC t J hJ hgap F w) := by
  apply ((insertionErrorCap_rapid gap C hC hgap).mul_power
    (Eventually.of_forall (fun w => by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
        ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val)))
    (B * Fintype.card (MaskOriginalBaseRow m gap t))).of_abs_le
  filter_upwards [insertion_difference_eventually_bound gap a ha C hC t J hJ hgap F B hF] with w hw
  exact hw.trans (le_abs_self _)

theorem source_insertion_difference_rapid
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
      (fun w => insertedCorrelation gap a ha C hC t J hJ hgap F w -
        unshiftedCorrelation gap a ha C hC t J hJ hgap F w) :=
  insertion_difference_rapid gap a ha C hC t J hJ hgap F 2
    (source_tests_eventually_sup_bound gap C hC t htail label F hroot hF)

theorem source_insertion_weighted_tendsto_zero
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
      (insertedCorrelation gap a ha C hC t J hJ hgap F w -
        unshiftedCorrelation gap a ha C hC t J hJ hgap F w)) atTop (𝓝 0) := by
  apply (Asymptotics.isLittleO_one_iff ℝ).mp
  simpa only [pow_zero, inv_one] using
    ((source_insertion_difference_rapid gap a ha C hC t J hJ hgap htail label F hroot hF).mul_power
      (Eventually.of_forall (fun w => by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
        ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val))) q) 0

end Hindman168.MaskOriginalSampling
