import Hindman168.MaskRemovalCoordinateDilation
import Hindman168.MaskBalancedCoordinates

/-! Actual balanced prime insertion. The fresh prime is first inserted
in v, then transferred in u with the original eta_p multiplier. Both
coordinates keep their original harmonic cutoff and outside law. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

noncomputable def maskStageBalancedPrimeAverage (k : ℕ) (u v : Fin (m + 1)) (w : ℕ)
    (H : MaskStagePoint S hS k → ℝ) : ℝ :=
  expectation (maskStageOuterMass S hS gap C k w) (fun r =>
    expectation (maskFreshPrimeMass (m := m) gap w) (fun p =>
      primeDivisorEta p (r.2 u) * H (r.1, maskBalancedCoordinates u v p r.2)))

noncomputable def maskBalancedPrimeInsertionErrorCap (u v : Fin (m + 1)) (B w : ℕ) : ℝ :=
  masterPrimeInsertionErrorCap (maskGeneratedMaster m gap) gap (maskOriginalPivotIndex C hC v) B w +
    ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
      masterPrimePairDilationErrorCap (maskGeneratedMaster m gap) gap (maskOriginalPivotIndex C hC u) w

theorem maskStagePrimeInsertedAverage_eq_primeAverage (k : ℕ) (v : Fin (m + 1)) (w : ℕ)
    (H : MaskStagePoint S hS k → ℝ) :
    maskStagePrimeInsertedAverage S hS gap C k v w H =
      expectation (maskFreshPrimeMass (m := m) gap w) (fun p =>
        maskStageCoordinateDilatedAverage S hS gap C k v w p H) := by
  unfold maskStagePrimeInsertedAverage maskStageCoordinateDilatedAverage
  rw [expectation_comm]

theorem maskStageBalancedPrimeAverage_eq_primeAverage (k : ℕ) (u v : Fin (m + 1)) (w : ℕ)
    (H : MaskStagePoint S hS k → ℝ) :
    maskStageBalancedPrimeAverage S hS gap C k u v w H =
      expectation (maskFreshPrimeMass (m := m) gap w) (fun p =>
        maskStagePrimeEtaAverage S hS gap C k u w p
          (fun r => H (r.1, maskBalancedCoordinates u v p r.2))) := by
  unfold maskStageBalancedPrimeAverage maskStagePrimeEtaAverage
  rw [expectation_comm]

theorem maskStageBalancedCoordinateDilatedAverage_cancel (k : ℕ) (u v : Fin (m + 1))
    (hne : u ≠ v) (w : ℕ) {p : ℕ} (hp : p ≠ 0) (H : MaskStagePoint S hS k → ℝ) :
    maskStageCoordinateDilatedAverage S hS gap C k u w p
        (fun r => H (r.1, maskBalancedCoordinates u v p r.2)) =
      maskStageCoordinateDilatedAverage S hS gap C k v w p H := by
  unfold maskStageCoordinateDilatedAverage
  simp only [maskBalancedCoordinates_dilation_cancel u v hne hp]

include hC hgap in
theorem maskStageBalancedPrimeInsertion_bound (k : ℕ) (u v : Fin (m + 1)) (hne : u ≠ v) (B : ℕ) :
    ∀ᶠ w in atTop, ∀ H : MaskStagePoint S hS k → ℝ,
      (∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support,
        ∀ z, |H (x,z)| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B) →
      |expectation (maskStageOuterMass S hS gap C k w) H -
        maskStageBalancedPrimeAverage S hS gap C k u v w H| ≤
      maskBalancedPrimeInsertionErrorCap gap C hC u v B w := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [maskStagePrimeInsertion_bound S hS gap C hC hgap k v B,
    maskStagePrimeEta_dilation_bound S hS gap C hC hgap k u B] with w hv hu
  intro H hH
  have hd := expectation_difference_support_bound (maskFreshPrimeMass (m := m) gap w)
    (primePoolMass_nonneg _ _)
    (fun p => maskStageCoordinateDilatedAverage S hS gap C k v w p H)
    (fun p => maskStagePrimeEtaAverage S hS gap C k u w p
      (fun r => H (r.1, maskBalancedCoordinates u v p r.2)))
    (((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
      masterPrimePairDilationErrorCap (maskGeneratedMaster m gap) gap (maskOriginalPivotIndex C hC u) w)
    (fun p hp => by
      have hpool := primePoolMass_support _ _ hp
      have he := hu p hpool (fun r => H (r.1, maskBalancedCoordinates u v p r.2))
        (fun x hx z => hH x hx _)
      rw [maskStageBalancedCoordinateDilatedAverage_cancel S hS gap C k u v hne w
        (primePool_mem.mp hpool).2.2.ne_zero] at he
      rw [abs_sub_comm]
      exact he)
  have ht : total (maskFreshPrimeMass (m := m) gap w) = 1 :=
    primePoolMass_total (hF.pool_positive_mass w (gap w).val)
  rw [ht, one_mul, ← maskStagePrimeInsertedAverage_eq_primeAverage,
    ← maskStageBalancedPrimeAverage_eq_primeAverage] at hd
  exact (abs_sub_le (expectation (maskStageOuterMass S hS gap C k w) H)
    (maskStagePrimeInsertedAverage S hS gap C k v w H)
    (maskStageBalancedPrimeAverage S hS gap C k u v w H)).trans (add_le_add (hv H hH) hd)

include hgap in
theorem maskBalancedPrimeInsertionErrorCap_tendsto (u v : Fin (m + 1)) (B : ℕ) :
    Tendsto (maskBalancedPrimeInsertionErrorCap gap C hC u v B) atTop (𝓝 0) := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  unfold maskBalancedPrimeInsertionErrorCap
  simpa only [zero_add] using
    (hF.prime_insertion_error_cap_tendsto gap (maskOriginalPivotIndex C hC v)
      (hgap.mono (fun w hw => hw v)) B).add
    (hF.prime_pair_dilation_weighted_cap_tendsto gap (maskOriginalPivotIndex C hC u)
      (hgap.mono (fun w hw => hw u)) B)

include hC hgap in
theorem maskStageBalancedPrimeInsertion_uniform_zero (k : ℕ) (u v : Fin (m + 1)) (hne : u ≠ v)
    (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ H : MaskStagePoint S hS k → ℝ,
      (∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support,
        ∀ z, |H (x,z)| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B) →
      |expectation (maskStageOuterMass S hS gap C k w) H -
        maskStageBalancedPrimeAverage S hS gap C k u v w H| < ε := by
  filter_upwards [maskStageBalancedPrimeInsertion_bound S hS gap C hC hgap k u v hne B,
    (maskBalancedPrimeInsertionErrorCap_tendsto gap C hC hgap u v B).eventually
      (eventually_lt_nhds hε)] with w hb he
  intro H hH
  exact (hb H hH).trans_lt he

end Hindman168
