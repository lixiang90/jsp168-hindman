import Hindman168.MaskRemovalStageWeightedSquares
import Hindman168.MasterPrimeDiagonalSampling

/-! Fresh-prime diagonal deletion at each actual intermediate mask stage.
The old tuple and all original harmonic coordinates remain in their
original laws. The error is uniform in every supported integrand with a
fixed polynomial bound after retaining the two divisor multipliers. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

noncomputable def maskOriginalPivotIndex (col : Fin (m + 1)) (w : ℕ) : Fin N :=
  ⟨(C w).pivot col, Finset.mem_range.mp (hC w col (by simp [Chain.block]))⟩

noncomputable def maskStageFreshPairAverage (k w : ℕ)
    (H : MaskStagePoint S hS k → ℕ × ℕ → ℝ) : ℝ :=
  expectation (maskStageOuterMass S hS gap C k w) (fun p =>
    expectation (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w)) (H p))

noncomputable def maskStageFreshOffDiagonalAverage (k w : ℕ)
    (H : MaskStagePoint S hS k → ℕ × ℕ → ℝ) : ℝ :=
  maskStageFreshPairAverage S hS gap C k w (fun p pq => if pq.1 ≠ pq.2 then H p pq else 0)

noncomputable def maskStageFreshDiagonalAverage (k w : ℕ)
    (H : MaskStagePoint S hS k → ℕ × ℕ → ℝ) : ℝ :=
  maskStageFreshPairAverage S hS gap C k w (fun p pq => if pq.1 = pq.2 then H p pq else 0)

noncomputable def maskStageFreshDiagonalMajorant (k : ℕ) (col : Fin (m + 1)) (w : ℕ) : ℝ :=
  maskStageFreshDiagonalAverage S hS gap C k w
    (fun p pq => primeDivisorEta pq.1 (p.2 col) * primeDivisorEta pq.2 (p.2 col))

noncomputable def maskFreshWeightedDiagonalCap (col : Fin (m + 1)) (w : ℕ) : ℝ :=
  masterPrimeDiagonalErrorCap (maskGeneratedMaster m gap) gap (maskOriginalPivotIndex C hC col) w

theorem maskStageFreshPairAverage_split (k w : ℕ)
    (H : MaskStagePoint S hS k → ℕ × ℕ → ℝ) :
    maskStageFreshPairAverage S hS gap C k w H =
      maskStageFreshOffDiagonalAverage S hS gap C k w H +
        maskStageFreshDiagonalAverage S hS gap C k w H := by
  unfold maskStageFreshOffDiagonalAverage maskStageFreshDiagonalAverage maskStageFreshPairAverage
  rw [← expectation_add]
  apply congrArg (expectation _)
  funext p
  rw [← expectation_add]
  apply congrArg (expectation _)
  funext pq
  by_cases h : pq.1 = pq.2 <;> simp [h]

include hC in
theorem maskStageFreshDiagonalMajorant_eq :
    ∀ᶠ w in atTop, ∀ k col,
    maskStageFreshDiagonalMajorant S hS gap C k col w =
      primeWeightedDiagonalMass ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper
        ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w) := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  have ht (col : Fin (m + 1)) : total (integerMass
      ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w)) = 1 :=
    integerMass_total (hw _ (hC w col (by simp [Chain.block]))).2.2
  intro k col
  unfold maskStageFreshDiagonalMajorant maskStageFreshDiagonalAverage maskStageFreshPairAverage
    maskStageOuterMass
  rw [expectation_conditionalJoint]
  have hb : expectation (maskOriginalBaseMass m gap C w) (fun z =>
      expectation (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w))
        (fun pq => if pq.1 = pq.2 then primeDivisorEta pq.1 (z col) * primeDivisorEta pq.2 (z col) else 0)) =
      primeWeightedDiagonalMass ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper
        ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w) :=
    by
      simpa only [maskOriginalBaseMass, maskFreshPrimeMass, primeWeightedDiagonalMass] using
        expectation_piMass_coordinate
          (fun j => integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot j)) (primorial w))
          ht col (fun z => expectation (tensor (maskFreshPrimeMass (m := m) gap w)
            (maskFreshPrimeMass (m := m) gap w)) (fun pq =>
              if pq.1 = pq.2 then primeDivisorEta pq.1 z * primeDivisorEta pq.2 z else 0))
  simp_rw [hb]
  rw [expectation_const]
  change total (masterPrimeSlotsMass (maskGeneratedMaster m gap) w
    (fun _ : Fin (maskPrefixRowStage S hS k).primeArity => (gap w).val)) * _ = _
  rw [hF.prime_slots_total, one_mul]

include hC in
theorem maskStageFreshDiagonalMajorant_eventually_cap :
    ∀ᶠ w in atTop, ∀ k col, maskStageFreshDiagonalMajorant S hS gap C k col w ≤
      maskFreshWeightedDiagonalCap gap C hC col w := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  have hall := eventually_all.mpr (fun col => hF.prime_diagonal_mass_eventually_bound gap
    (maskOriginalPivotIndex C hC col))
  filter_upwards [maskStageFreshDiagonalMajorant_eq S hS gap C hC, hall] with w he hb
  intro k col
  rw [he k col]
  exact hb col

include hgap in
theorem maskFreshWeightedDiagonalCap_weighted_tendsto (col : Fin (m + 1)) (B : ℕ) :
    Tendsto (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
      maskFreshWeightedDiagonalCap gap C hC col w) atTop (𝓝 0) := by
  exact (maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)).prime_diagonal_weighted_cap_tendsto
    gap (maskOriginalPivotIndex C hC col) (hgap.mono (fun w hw => hw col)) B

include hC in
theorem maskStageFreshDiagonalAverage_bound (k : ℕ) (col : Fin (m + 1)) (B : ℕ) :
    ∀ᶠ w in atTop, ∀ H : MaskStagePoint S hS k → ℕ × ℕ → ℝ,
      (∀ p ∈ (maskStageOuterMass S hS gap C k w).support,
        ∀ pq ∈ (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w)).support,
        |H p pq| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
          (primeDivisorEta pq.1 (p.2 col) * primeDivisorEta pq.2 (p.2 col))) →
      |maskStageFreshDiagonalAverage S hS gap C k w H| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
          maskFreshWeightedDiagonalCap gap C hC col w := by
  filter_upwards [maskStageOuterMass_eventually_nonneg S hS gap C hC,
    maskStageFreshDiagonalMajorant_eventually_cap S hS gap C hC] with w hμ hc
  intro H hH
  have hd : |maskStageFreshDiagonalAverage S hS gap C k w H| ≤
      maskStageFreshDiagonalAverage S hS gap C k w (fun p pq =>
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
          (primeDivisorEta pq.1 (p.2 col) * primeDivisorEta pq.2 (p.2 col))) := by
    unfold maskStageFreshDiagonalAverage maskStageFreshPairAverage
    apply abs_expectation_le_majorant_support _ _ _ (hμ k)
    intro p hp
    apply abs_expectation_le_majorant_support _ _ _
      (tensor_nonneg _ _ (primePoolMass_nonneg _ _) (primePoolMass_nonneg _ _))
    intro pq hpq
    by_cases he : pq.1 = pq.2
    · simp only [if_pos he]
      exact hH p hp pq hpq
    · simp only [if_neg he, abs_zero, le_refl]
  have he : maskStageFreshDiagonalAverage S hS gap C k w (fun p pq =>
      ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
        (primeDivisorEta pq.1 (p.2 col) * primeDivisorEta pq.2 (p.2 col))) =
      ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
        maskStageFreshDiagonalMajorant S hS gap C k col w := by
    unfold maskStageFreshDiagonalMajorant
    unfold maskStageFreshDiagonalAverage maskStageFreshPairAverage
    have hi (p : MaskStagePoint S hS k) (pq : ℕ × ℕ) :
        (if pq.1 = pq.2 then ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
          (primeDivisorEta pq.1 (p.2 col) * primeDivisorEta pq.2 (p.2 col)) else 0) =
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
          (if pq.1 = pq.2 then primeDivisorEta pq.1 (p.2 col) * primeDivisorEta pq.2 (p.2 col) else 0) := by
      split_ifs <;> simp only [mul_zero]
    simp_rw [hi, expectation_const_mul]
  rw [he] at hd
  exact hd.trans (mul_le_mul_of_nonneg_left (hc k col) (by positivity))

include hC in
theorem maskStageFreshOffDiagonal_deletion (k : ℕ) (col : Fin (m + 1)) (B : ℕ) :
    ∀ᶠ w in atTop, ∀ H : MaskStagePoint S hS k → ℕ × ℕ → ℝ,
      (∀ p ∈ (maskStageOuterMass S hS gap C k w).support,
        ∀ pq ∈ (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w)).support,
        |H p pq| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
          (primeDivisorEta pq.1 (p.2 col) * primeDivisorEta pq.2 (p.2 col))) →
      |maskStageFreshPairAverage S hS gap C k w H - maskStageFreshOffDiagonalAverage S hS gap C k w H| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
          maskFreshWeightedDiagonalCap gap C hC col w := by
  filter_upwards [maskStageFreshDiagonalAverage_bound S hS gap C hC k col B] with w hw
  intro H hH
  rw [maskStageFreshPairAverage_split, add_sub_cancel_left]
  exact hw H hH

include hC hgap in
theorem maskStageFreshOffDiagonal_deletion_uniform_zero (k : ℕ) (col : Fin (m + 1)) (B : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ H : MaskStagePoint S hS k → ℕ × ℕ → ℝ,
      (∀ p ∈ (maskStageOuterMass S hS gap C k w).support,
        ∀ pq ∈ (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w)).support,
        |H p pq| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
          (primeDivisorEta pq.1 (p.2 col) * primeDivisorEta pq.2 (p.2 col))) →
      |maskStageFreshPairAverage S hS gap C k w H - maskStageFreshOffDiagonalAverage S hS gap C k w H| < ε := by
  filter_upwards [maskStageFreshOffDiagonal_deletion S hS gap C hC k col B,
    (maskFreshWeightedDiagonalCap_weighted_tendsto gap C hC hgap col B).eventually
      (eventually_lt_nhds hε)] with w hb he
  intro H hH
  exact (hb H hH).trans_lt he

end Hindman168
