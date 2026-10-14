import Hindman168.MaskOriginalOrderedPrefactors

/-! The actual original weighted ordered recurrence now has one constant
that depends only on the original column parameter. Its initial stage is
exactly the independent single-shift correlation. The terminal stage still
retains all nonroot majorants; no cancellation is performed here. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def maskAdditiveRecurrenceBound (m : ℕ) : ℝ :=
  maskAdditivePrefactorCap m ^ (2 ^ maskRowCountBound m - 1)

theorem maskAdditiveRecurrenceBound_ge_one (m : ℕ) : 1 ≤ maskAdditiveRecurrenceBound m :=
  one_le_pow₀ (maskAdditivePrefactorCap_ge_one m)

namespace MaskOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

local notation "χ" => outsideMass gap a ha C hC t J hJ hgap
local notation "ν" => completedDirectionMass gap a ha C hC t J hJ hgap

noncomputable def orderedAverage (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w j : ℕ) : ℝ :=
  AdditiveRowData.orderedAverage (χ w) (ν w)
    (fun p => additiveData gap a C t w p.1) Prod.snd
    (completedTest gap t F w) (completedMajorant gap C t label w) j

theorem orderedAverage_power_bound_eventually
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤
        rowMajorant gap C t label w (some (additiveRowAssigned _ k)) y) :
    ∀ᶠ w in atTop,
      |orderedAverage gap a ha C hC t J hJ hgap label F w 0| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) ≤
      maskAdditiveRecurrenceBound m *
        |orderedAverage gap a ha C hC t J hJ hgap label F w
          (Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target))| := by
  filter_upwards [outside_probability_eventually gap a ha C hC t J hJ hgap,
    completed_direction_probability_eventually gap a ha C hC t J hJ hgap,
    orderedPrefactorCap_eventually_le gap a ha C hC t J hJ hgap htail label, hF] with w hp hd hc hf
  let b := Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)
  have hbound := completed_test_bound gap C t label F w hf
  have hstep := AdditiveRowData.ordered_average_power_bound (b := b) (χ w) hp.1 (ν w) hd.1 hd.2
    (fun p => additiveData gap a C t w p.1) Prod.snd
    (completedTest gap t F w) (completedMajorant gap C t label w) hbound
  have hn : 0 ≤ orderedPrefactorCap gap a ha C hC t J hJ hgap label w :=
    AdditiveRowData.orderedPrefactorCap_nonneg (χ w) (ν w)
      (fun p => additiveData gap a C t w p.1) Prod.snd (completedMajorant gap C t label w)
  have hb : b ≤ maskRowCountBound m := maskGenerated_additive_dimension_le m gap t
  have he : 2 ^ b - 1 ≤ 2 ^ maskRowCountBound m - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb) 1
  have hpow : (orderedPrefactorCap gap a ha C hC t J hJ hgap label w) ^ (2 ^ b - 1) ≤
      maskAdditiveRecurrenceBound m :=
    (pow_le_pow_left₀ hn hc _).trans (pow_le_pow_right₀ (maskAdditivePrefactorCap_ge_one m) he)
  exact hstep.trans (mul_le_mul_of_nonneg_right hpow (abs_nonneg _))

theorem orderedAverage_initial_single_eventually
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ) :
    ∀ᶠ w in atTop, orderedAverage gap a ha C hC t J hJ hgap label F w 0 =
      expectation (χ w) (fun p => expectation (piMass (ν w p))
        (fun u => ∏ i : MaskOriginalBaseRow m gap t,
          completedTest gap t F w p i ((additiveData gap a C t w p.1).form i
            (fun col => p.2 col + ∑ k, u k * (additiveData gap a C t w p.1).direction k col)))) := by
  filter_upwards [completed_direction_probability_eventually gap a ha C hC t J hJ hgap] with w hw
  exact AdditiveRowData.orderedAverage_initial_single (χ w) (ν w) hw.2
    (fun p => additiveData gap a C t w p.1) Prod.snd
    (completedTest gap t F w) (completedMajorant gap C t label w)

end MaskOriginalSampling
end Hindman168
