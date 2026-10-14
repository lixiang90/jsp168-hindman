import Hindman168.MasterPrimeJointDilation
import Hindman168.MaskRemovalPrimeInsertion

/-! Fixed one- and two-prime harmonic dilation on each actual mask outer
law. The old-prime tuple and all other original coordinates are integrated
with their unchanged outside probability law. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

noncomputable def maskStageCoordinateDilatedAverage (k : ℕ) (col : Fin (m + 1)) (w t : ℕ)
    (H : MaskStagePoint S hS k → ℝ) : ℝ :=
  expectation (maskStageOuterMass S hS gap C k w) (fun r =>
    H (r.1, Function.update r.2 col ((t : ℤ) * r.2 col)))

noncomputable def maskStagePrimeEtaAverage (k : ℕ) (col : Fin (m + 1)) (w p : ℕ)
    (H : MaskStagePoint S hS k → ℝ) : ℝ :=
  expectation (maskStageOuterMass S hS gap C k w) (fun r => primeDivisorEta p (r.2 col) * H r)

noncomputable def maskStagePrimePairEtaAverage (k : ℕ) (col : Fin (m + 1)) (w p q : ℕ)
    (H : MaskStagePoint S hS k → ℝ) : ℝ :=
  expectation (maskStageOuterMass S hS gap C k w) (fun r =>
    primeDivisorEta p (r.2 col) * primeDivisorEta q (r.2 col) * H r)

theorem maskStageCoordinateDilatedAverage_pivot (k : ℕ) (col : Fin (m + 1)) (w t : ℕ)
    (H : MaskStagePoint S hS k → ℝ) :
    maskStageCoordinateDilatedAverage S hS gap C k col w t H =
      expectation (maskStagePrimeInsertionOutsideMass S hS gap C k col w) (fun r =>
        expectation (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
          (fun z => maskStagePivotTest S hS k col H r ((t : ℤ) * z))) := by
  rw [maskStageCoordinateDilatedAverage, maskStageAverage_pivot S hS gap C k col w]
  unfold maskStagePivotTest
  simp only [insertPivotCoordinate_self, update_insertPivotCoordinate]

theorem maskStagePrimeEtaAverage_pivot (k : ℕ) (col : Fin (m + 1)) (w p : ℕ)
    (H : MaskStagePoint S hS k → ℝ) :
    maskStagePrimeEtaAverage S hS gap C k col w p H =
      expectation (maskStagePrimeInsertionOutsideMass S hS gap C k col w) (fun r =>
        expectation (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
          (fun z => primeDivisorEta p z * maskStagePivotTest S hS k col H r z)) := by
  rw [maskStagePrimeEtaAverage, maskStageAverage_pivot S hS gap C k col w]
  unfold maskStagePivotTest
  simp only [insertPivotCoordinate_self]

theorem maskStagePrimePairEtaAverage_pivot (k : ℕ) (col : Fin (m + 1)) (w p q : ℕ)
    (H : MaskStagePoint S hS k → ℝ) :
    maskStagePrimePairEtaAverage S hS gap C k col w p q H =
      expectation (maskStagePrimeInsertionOutsideMass S hS gap C k col w) (fun r =>
        expectation (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
          (fun z => primeDivisorEta p z * primeDivisorEta q z * maskStagePivotTest S hS k col H r z)) := by
  rw [maskStagePrimePairEtaAverage, maskStageAverage_pivot S hS gap C k col w]
  unfold maskStagePivotTest
  simp only [insertPivotCoordinate_self]

include hC hgap in
theorem maskStagePrimeEta_dilation_bound (k : ℕ) (col : Fin (m + 1)) (B : ℕ) :
    ∀ᶠ w in atTop,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ H : MaskStagePoint S hS k → ℝ,
      (∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support,
        ∀ z, |H (x,z)| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B) →
      |maskStagePrimeEtaAverage S hS gap C k col w p H -
        maskStageCoordinateDilatedAverage S hS gap C k col w p H| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
          masterPrimePairDilationErrorCap (maskGeneratedMaster m gap) gap
            (maskOriginalPivotIndex C hC col) w := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.prime_single_eta_dilation_outside_bound
    (ι := MaskInsertionOutsidePoint S hS k col) gap (maskOriginalPivotIndex C hC col)
    (hgap.mono (fun w hw => hw col)) B,
    maskStagePrimeInsertionOutsideMass_eventually_probability S hS gap C hC] with w hb hprob
  intro p hp H hH
  rw [maskStagePrimeEtaAverage_pivot, maskStageCoordinateDilatedAverage_pivot]
  apply hb _ (hprob k col).1 (hprob k col).2 p hp
  intro r hr z
  have hx := (Finset.mem_product.mp (tensor_support _ _ hr)).1
  exact hH r.1 hx _

include hC hgap in
theorem maskStagePrimePairEta_dilation_bound (k : ℕ) (col : Fin (m + 1)) (B : ℕ) :
    ∀ᶠ w in atTop,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper, p ≠ q →
      ∀ H : MaskStagePoint S hS k → ℝ,
      (∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support,
        ∀ z, |H (x,z)| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B) →
      |maskStagePrimePairEtaAverage S hS gap C k col w p q H -
        maskStageCoordinateDilatedAverage S hS gap C k col w (p*q) H| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
          masterPrimePairDilationErrorCap (maskGeneratedMaster m gap) gap
            (maskOriginalPivotIndex C hC col) w := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.distinct_prime_eta_dilation_outside_bound
    (ι := MaskInsertionOutsidePoint S hS k col) gap (maskOriginalPivotIndex C hC col)
    (hgap.mono (fun w hw => hw col)) B,
    maskStagePrimeInsertionOutsideMass_eventually_probability S hS gap C hC] with w hb hprob
  intro p hp q hq hne H hH
  rw [maskStagePrimePairEtaAverage_pivot, maskStageCoordinateDilatedAverage_pivot]
  apply hb _ (hprob k col).1 (hprob k col).2 p hp q hq hne
  intro r hr z
  have hx := (Finset.mem_product.mp (tensor_support _ _ hr)).1
  exact hH r.1 hx _

include hC hgap in
theorem maskStagePrimePairEta_dilation_uniform_zero (k : ℕ) (col : Fin (m + 1)) (B : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper, p ≠ q →
      ∀ H : MaskStagePoint S hS k → ℝ,
      (∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support,
        ∀ z, |H (x,z)| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B) →
      |maskStagePrimePairEtaAverage S hS gap C k col w p q H -
        maskStageCoordinateDilatedAverage S hS gap C k col w (p*q) H| < ε := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [maskStagePrimePairEta_dilation_bound S hS gap C hC hgap k col B,
    (hF.prime_pair_dilation_weighted_cap_tendsto gap (maskOriginalPivotIndex C hC col)
      (hgap.mono (fun w hw => hw col)) B).eventually (eventually_lt_nhds hε)] with w hb he
  intro p hp q hq hne H hH
  exact (hb p hp q hq hne H hH).trans_lt he

end Hindman168
