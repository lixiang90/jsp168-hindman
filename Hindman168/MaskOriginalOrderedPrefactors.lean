import Hindman168.MaskOriginalAdditiveData

/-! The computed ordered prefactors are the actual normalized stage
integrals. Their positivity and simultaneous linear-forms bounds yield a
cap depending only on m for the original weighted finite recurrence. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def maskAdditivePrefactorCap (m : ℕ) : ℝ :=
  1 + (maskRowCountBound m : ℝ) * maskCopiedMajorantBound m

theorem maskAdditivePrefactorCap_ge_one (m : ℕ) : 1 ≤ maskAdditivePrefactorCap m := by
  unfold maskAdditivePrefactorCap
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (maskCopiedMajorantBound_pos m).le)

namespace MaskOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

local notation "S" => maskOriginalSampling m gap a ha C hC t J hJ hgap
local notation "χ" => outsideMass gap a ha C hC t J hJ hgap
local notation "ν" => completedDirectionMass gap a ha C hC t J hJ hgap

noncomputable def orderedPrefactor (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) (k : MaskOriginalDirection m gap t) : ℝ :=
  AdditiveRowData.orderedPrefactor (χ w) (ν w)
    (fun p => additiveData gap a C t w p.1) Prod.snd (completedMajorant gap C t label w) k

noncomputable def orderedPrefactorCap (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) : ℝ :=
  AdditiveRowData.orderedPrefactorCap (χ w) (ν w)
    (fun p => additiveData gap a C t w p.1) Prod.snd (completedMajorant gap C t label w)

theorem orderedPrefactor_eventually_eq_normalized
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, ∀ k : MaskOriginalDirection m gap t,
      orderedPrefactor gap a ha C hC t J hJ hgap label w k =
        (S).normalizedStagePrefactor label w (predictionDirectionPrefix _ k.val)
          (some (additiveRowAssigned _ k)) := by
  filter_upwards [additiveData_eventually_certificate gap a ha C hC t] with w hw
  intro k
  rw [normalizedStagePrefactor_eq_joint gap a ha C hC t J hJ hgap label w]
  unfold orderedPrefactor AdditiveRowData.orderedPrefactor outsideMass
  rw [expectation_conditionalJoint, expectation_conditionalJoint]
  apply expectation_congr_support
  intro x hx
  have hxG := conditionMass_mem_support_event ((S).primeMass w)
    (maskGeneratedCopiedPrimeGood m gap t w) x hx
  obtain ⟨H, hD⟩ := hw x hxG
  apply congrArg (expectation (maskOriginalBaseMass m gap C w))
  funext z
  apply congrArg (expectation (piMass (fun i => tensor (ν w (x, z) i) (ν w (x, z) i))))
  funext v
  have hΩ : completedMajorant gap C t label w (x, z) (some (additiveRowAssigned _ k)) =
      rowMajorant gap C t label w (some (additiveRowAssigned _ k)) :=
    funext (fun _ => if_pos hxG)
  let b := Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)
  have eD := congrArg (fun D : AdditiveRowData b (m + 1) => D.stageFactorProduct
    (predictionDirectionPrefix b k.val) (some (additiveRowAssigned b k)) z (predictionPairValues v)
    (completedMajorant gap C t label w (x, z) (some (additiveRowAssigned b k)))) hD
  have eΩ := congrArg (fun f : ℤ → ℝ => H.data.stageFactorProduct
    (predictionDirectionPrefix b k.val) (some (additiveRowAssigned b k)) z (predictionPairValues v) f) hΩ
  exact eD.trans (eΩ.trans ((S).stage_product_identification label w x H
    (predictionDirectionPrefix b k.val) (some (additiveRowAssigned b k)) z v))

theorem orderedPrefactor_eventually_nonneg
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, ∀ k, 0 ≤ orderedPrefactor gap a ha C hC t J hJ hgap label w k := by
  filter_upwards [outside_probability_eventually gap a ha C hC t J hJ hgap,
    completed_direction_probability_eventually gap a ha C hC t J hJ hgap,
    completed_majorant_eventually_nonneg gap C hC t label] with w hp hd hΩ
  intro k
  exact AdditiveRowData.orderedPrefactor_nonneg (χ w) hp.1 (ν w) hd.1
    (fun p => additiveData gap a C t w p.1) Prod.snd (completedMajorant gap C t label w)
    (fun p i y => hΩ p (some (additiveRowAssigned _ i)) y) k

theorem orderedPrefactors_eventually_le
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, ∀ k,
      orderedPrefactor gap a ha C hC t J hJ hgap label w k ≤ maskCopiedMajorantBound m := by
  filter_upwards [orderedPrefactor_eventually_eq_normalized gap a ha C hC t J hJ hgap label,
    all_normalizedStagePrefactors_eventually_le gap a ha C hC t J hJ hgap htail label] with w he hb
  intro k
  rw [he k]
  exact hb _ _

theorem orderedPrefactorCap_eventually_le
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, orderedPrefactorCap gap a ha C hC t J hJ hgap label w ≤ maskAdditivePrefactorCap m := by
  filter_upwards [orderedPrefactor_eventually_nonneg gap a ha C hC t J hJ hgap label,
    orderedPrefactors_eventually_le gap a ha C hC t J hJ hgap htail label] with w hn hb
  change 1 + ∑ k : MaskOriginalDirection m gap t,
    |orderedPrefactor gap a ha C hC t J hJ hgap label w k| ≤
      1 + (maskRowCountBound m : ℝ) * maskCopiedMajorantBound m
  simp_rw [abs_of_nonneg (hn _)]
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (MaskOriginalDirection m gap t))) => hb k)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hc : (Fintype.card (PolynomialRowFamily.OffTargetRow
      (maskGeneratedRowDataFamily m gap t).target) : ℝ) ≤ maskRowCountBound m := by
    exact_mod_cast maskGenerated_additive_dimension_le m gap t
  have hh := hs.trans (mul_le_mul_of_nonneg_right hc (maskCopiedMajorantBound_pos m).le)
  linarith

end MaskOriginalSampling
end Hindman168
