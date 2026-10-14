import Hindman168.MaskOriginalWeightedRecurrence

/-! The original inserted correlation and the actual target cube times
all retained majorants. The proved m-only recurrence is applied to these
integrands under the original normalized joint law. No retained majorant
is removed or replaced by its mean. -/

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

noncomputable def insertedCorrelation
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) : ℝ :=
  expectation (χ w) (fun p => expectation (piMass (ν w p))
    (fun u => ∏ i : MaskOriginalBaseRow m gap t, F w p.1 i
      ((maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerLinearForm p.1
        (masterColumnCoefficient N a (fun w => (C w).block) w)
        (PolynomialRowFamily.additiveIndexEquiv (maskGeneratedRowDataFamily m gap t).target i)
        (fun col => p.2 col + ∑ k, u k *
          (maskGeneratedRowDataFamily m gap t).rows.integerTranslation (maskGeneratedMaster m gap) w
            (masterColumnCoefficient N a (fun w => (C w).block) w) p.1
            (maskGeneratedRowDataFamily m gap t).target
            (PolynomialRowFamily.additiveIndexEquiv (maskGeneratedRowDataFamily m gap t).target
              (some (additiveRowAssigned _ k))) col))))

theorem orderedAverage_initial_eq_inserted
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ) :
    ∀ᶠ w in atTop, orderedAverage gap a ha C hC t J hJ hgap label F w 0 =
      insertedCorrelation gap a ha C hC t J hJ hgap F w := by
  filter_upwards [orderedAverage_initial_single_eventually gap a ha C hC t J hJ hgap label F,
    additiveData_eventually_certificate gap a ha C hC t] with w hi hd
  rw [hi]
  unfold insertedCorrelation outsideMass
  rw [expectation_conditionalJoint, expectation_conditionalJoint]
  apply expectation_congr_support
  intro x hx
  have hxG := conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) x hx
  obtain ⟨H, hD⟩ := hd x hxG
  apply congrArg (expectation (maskOriginalBaseMass m gap C w))
  funext z
  apply congrArg (expectation (piMass (ν w (x, z))))
  funext u
  apply Fintype.prod_congr
  intro i
  have hF : completedTest gap t F w (x, z) i = F w x i := funext (fun _ => if_pos hxG)
  rw [hF, hD]
  refine congrArg (F w x i) ((H.form_eq i _).trans ?_)
  apply congrArg ((maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerLinearForm x
    (masterColumnCoefficient N a (fun w => (C w).block) w)
    (PolynomialRowFamily.additiveIndexEquiv (maskGeneratedRowDataFamily m gap t).target i))
  funext col
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun q : ℤ => u k * q) (H.direction_eq k col)

noncomputable def targetCube
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) (p : MaskOriginalPoint m gap t) (v : MaskOriginalDirection m gap t → ℤ × ℤ) : ℝ :=
  ∏ η : MaskOriginalDirection m gap t → Bool, F w p.1 none
    ((maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerLinearForm p.1
      (masterColumnCoefficient N a (fun w => (C w).block) w) (maskGeneratedRowDataFamily m gap t).target p.2 +
      ((maskGeneratedRowDataFamily m gap t).rows.translationModulus (maskGeneratedMaster m gap) w p.1
        (maskGeneratedRowDataFamily m gap t).target : ℤ) * ∑ k, predictionPairValues v k (η k))

noncomputable def retainedMajorant (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) (p : MaskOriginalPoint m gap t) (v : MaskOriginalDirection m gap t → ℤ × ℤ) : ℝ :=
  ∏ i : {r : MaskOriginalBaseRow m gap t // r ≠ none},
    (additiveData gap a C t w p.1).stageFactorProduct Finset.univ i.val p.2 (predictionPairValues v)
      (rowMajorant gap C t label w i.val)

include hC in
theorem retainedMajorant_eventually_nonneg (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, ∀ p v, 0 ≤ retainedMajorant gap a C t label w p v := by
  filter_upwards [rowMajorant_eventually_nonneg gap C hC t label] with w hw
  intro p v
  unfold retainedMajorant
  apply Finset.prod_nonneg
  intro i _
  unfold AdditiveRowData.stageFactorProduct
  exact Finset.prod_nonneg (fun _ _ => hw i.val _)

include ha hC in
theorem terminal_integrand_actual
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ z v,
      (additiveData gap a C t w x).eliminationIntegrand Finset.univ z v
        (completedTest gap t F w (x, z)) (completedMajorant gap C t label w (x, z)) =
      targetCube gap a C t F w (x, z) v * retainedMajorant gap a C t label w (x, z) v := by
  filter_upwards [additiveData_eventually_certificate gap a ha C hC t] with w hw
  intro x hxG z v
  obtain ⟨H, hD⟩ := hw x hxG
  have hF : completedTest gap t F w (x, z) = F w x := funext (fun _ => funext (fun _ => if_pos hxG))
  have hΩ : completedMajorant gap C t label w (x, z) = rowMajorant gap C t label w :=
    funext (fun _ => funext (fun _ => if_pos hxG))
  unfold targetCube retainedMajorant
  rw [hD, hF, hΩ]
  exact H.terminal_cube z v (F w x) (rowMajorant gap C t label w)

noncomputable def terminalAverage (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) : ℝ :=
  expectation (χ w) (fun p => expectation (piMass (fun k => tensor (ν w p k) (ν w p k)))
    (fun v => targetCube gap a C t F w p v * retainedMajorant gap a C t label w p v))

theorem orderedAverage_terminal_eq_actual
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ) :
    ∀ᶠ w in atTop,
      orderedAverage gap a ha C hC t J hJ hgap label F w
        (Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) =
      terminalAverage gap a ha C hC t J hJ hgap label F w := by
  filter_upwards [terminal_integrand_actual gap a ha C hC t label F] with w hw
  let b := Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)
  change expectation (χ w) (fun p =>
    expectation (piMass (fun k => tensor (ν w p k) (ν w p k))) (fun v =>
      (additiveData gap a C t w p.1).eliminationIntegrand (predictionDirectionPrefix b b)
        p.2 v (completedTest gap t F w p) (completedMajorant gap C t label w p))) =
    expectation (χ w) (fun p =>
      expectation (piMass (fun k => tensor (ν w p k) (ν w p k))) (fun v =>
        targetCube gap a C t F w p v * retainedMajorant gap a C t label w p v))
  rw [predictionDirectionPrefix_full]
  unfold outsideMass
  rw [expectation_conditionalJoint, expectation_conditionalJoint]
  apply expectation_congr_support
  intro x hx
  have hxG := conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) x hx
  apply congrArg (expectation (maskOriginalBaseMass m gap C w))
  funext z
  apply congrArg (expectation (piMass (fun k => tensor (ν w (x, z) k) (ν w (x, z) k))))
  funext v
  exact hw x hxG z v

theorem inserted_correlation_power_bound
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) :
    ∀ᶠ w in atTop,
      |insertedCorrelation gap a ha C hC t J hJ hgap F w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) ≤
      maskAdditiveRecurrenceBound m * |terminalAverage gap a ha C hC t J hJ hgap label F w| := by
  filter_upwards [orderedAverage_power_bound_eventually gap a ha C hC t J hJ hgap htail label F hF,
    orderedAverage_initial_eq_inserted gap a ha C hC t J hJ hgap label F,
    orderedAverage_terminal_eq_actual gap a ha C hC t J hJ hgap label F] with w hb hi ht
  simpa only [hi, ht] using hb

end Hindman168.MaskOriginalSampling
