import Hindman168.FiniteConditionedSubsetBound
import Hindman168.MaskEndpointShortCubeIdentity
import Hindman168.MaskUniformDetectionThreshold

/-! Remove the additional local denominator exclusion with its proved
positive event mass, then detect the actual original subset correlation
using the original short-cube statistic. The tolerance precedes N. -/

namespace Hindman168
open Filter FiniteMass MaskOriginalSampling
open scoped Topology Classical

theorem maskLocalPrimeGood_event_tendsto_one {m N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    Tendsto (fun w => event
      (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
        ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper)
      (predictionLocalPrimeGoodEvent (maskGeneratedMaster m gap)
        ((maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target)
        (targetPredictionPolynomial gap t) w)) atTop (𝓝 1) := by
  let T := maskGeneratedRowDataFamily m gap t
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  exact hF.local_prime_good_event_tendsto_one (T.rows.catalog T.target)
    (T.rows.denominator T.target) (T.rows.denominator_mem_catalog T.target)
    T.slot T.slot_injective
    (fun f hf => originalRowMasterCatalog_inclusion (maskGeneratedRowDataFamily m gap) t f hf) gap

theorem maskEndpointTargetCube_abs_le_twice_primeGood_shortCube {m N : ℕ}
    (gap : ℕ → Fin N) (C : ℕ → Chain (m+1))
    (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) :
    ∀ᶠ w in atTop, ∀ g : ℤ → ℝ,
      |maskEndpointTargetCube gap C t J w g| ≤ 2 *
        expectation (conditionMass
          (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
            ((maskGeneratedMaster m gap).pool w (gap w).val).lower
            ((maskGeneratedMaster m gap).pool w (gap w).val).upper)
          (primeSampleGood ((maskGeneratedRowDataFamily m gap t).rows.catalog
            (maskGeneratedRowDataFamily m gap t).target))) (fun x =>
          |integerPredictionShortCubeStatistic w ((maskGeneratedMaster m gap).modulus w : ℕ)
            ((maskGeneratedMaster m gap).gap w (gap w).val)
            ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t)))
            (targetPredictionOrder gap t) J (targetPredictionPolynomial gap t) g x|) := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [(maskLocalPrimeGood_event_tendsto_one gap t).eventually
    (eventually_gt_nhds (by norm_num : (1 : ℝ)/2 < 1))] with w hw
  intro g
  have hb := maskEndpointTargetCube_abs_le_integer_shortCube gap C t J w g
  rw [maskRootPrimeMass_eq_original_dual] at hb
  exact hb.trans (conditioned_subset_expectation_le_twice _ _ _
    (primeIndependentMass_nonneg _ _ _)
    (primeIndependentMass_total (hF.pool_positive_mass w (gap w).val))
    (fun _ hx => hx.1) hw.le _ (fun _ => abs_nonneg _))

theorem maskOriginalSubset_shortCube_detection_threshold (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {N : ℕ}
      (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (_ha : ∀ col, 0 < a col)
      (C : ℕ → Chain (m+1)) (_hC : ∀ w col, (C w).block col ⊆ Finset.range N)
      (J : ℕ) (_hJ : 0 < J)
      (_hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
      (_htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val),
      ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
        ∀ f : NonemptyColumnSubset (m+1) → ℤ → ℝ,
        ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
        maskOriginalSubsetAdmissible gap C w f b →
        expectation (conditionMass
          (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
            ((maskGeneratedMaster m gap).pool w (gap w).val).lower
            ((maskGeneratedMaster m gap).pool w (gap w).val).upper)
          (primeSampleGood ((maskGeneratedRowDataFamily m gap t).rows.catalog
            (maskGeneratedRowDataFamily m gap t).target))) (fun x =>
          |integerPredictionShortCubeStatistic w ((maskGeneratedMaster m gap).modulus w : ℕ)
            ((maskGeneratedMaster m gap).gap w (gap w).val)
            ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t)))
            (targetPredictionOrder gap t) J (targetPredictionPolynomial gap t)
            (f (maskSourceNonemptySupport m t)) x|) ≤ δ →
        |maskOriginalSubsetCorrelation gap a C w f b| ≤ ε := by
  refine ⟨maskUniformDetectionTolerance m ε / 2, by
    exact div_pos (maskUniformDetectionTolerance_pos m hε) (by norm_num), ?_⟩
  intro N gap a ha C hC J hJ hgap htail
  have hb : ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)), ∀ g : ℤ → ℝ,
      |maskEndpointTargetCube gap C t J w g| ≤ 2 *
        expectation (conditionMass
          (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
            ((maskGeneratedMaster m gap).pool w (gap w).val).lower
            ((maskGeneratedMaster m gap).pool w (gap w).val).upper)
          (primeSampleGood ((maskGeneratedRowDataFamily m gap t).rows.catalog
            (maskGeneratedRowDataFamily m gap t).target))) (fun x =>
          |integerPredictionShortCubeStatistic w ((maskGeneratedMaster m gap).modulus w : ℕ)
            ((maskGeneratedMaster m gap).gap w (gap w).val)
            ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t)))
            (targetPredictionOrder gap t) J (targetPredictionPolynomial gap t) g x|) :=
    eventually_all.mpr (fun t => maskEndpointTargetCube_abs_le_twice_primeGood_shortCube gap C t J)
  filter_upwards [hb, maskOriginalSubset_detection_before_master gap a ha C hC J hJ hgap htail hε]
    with w hbw hd
  intro t f b hf hshort
  apply hd t f b hf
  have h := hbw t (f (maskSourceNonemptySupport m t))
  linarith

end Hindman168
