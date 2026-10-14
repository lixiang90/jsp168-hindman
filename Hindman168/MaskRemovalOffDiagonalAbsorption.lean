import Hindman168.MaskRemovalBalancedInsertion

/-! Off-diagonal pq absorption on the actual shared old-prime/base law.
The two fresh primes retain their independent original weights. The
absorbed balanced coordinates are exactly (q,p) and (p,q). -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

theorem maskStageFreshOffDiagonalAverage_expectation (k w : ℕ)
    (H : MaskStagePoint S hS k → ℕ × ℕ → ℝ) :
    maskStageFreshOffDiagonalAverage S hS gap C k w H =
      expectation (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w))
        (fun pq => if pq.1 ≠ pq.2 then
          expectation (maskStageOuterMass S hS gap C k w) (fun r => H r pq) else 0) := by
  unfold maskStageFreshOffDiagonalAverage maskStageFreshPairAverage
  rw [expectation_comm]
  apply congrArg (expectation _)
  funext pq
  by_cases h : pq.1 ≠ pq.2
  · simp only [if_pos h]
  · simp only [if_neg h, expectation_const, mul_zero]

include hC hgap in
theorem maskStageOffDiagonalAbsorption_bound (k : ℕ) (col : Fin (m + 1)) (B : ℕ) :
    ∀ᶠ w in atTop, ∀ H : MaskStagePoint S hS k → ℕ × ℕ → ℝ,
      (∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support,
        ∀ pq ∈ (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w)).support,
        ∀ z, |H (x,z) pq| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B) →
      |maskStageFreshOffDiagonalAverage S hS gap C k w
          (fun r pq => primeDivisorEta pq.1 (r.2 col) * primeDivisorEta pq.2 (r.2 col) * H r pq) -
        maskStageFreshOffDiagonalAverage S hS gap C k w
          (fun r pq => H (r.1, Function.update r.2 col (((pq.1*pq.2 : ℕ) : ℤ) * r.2 col)) pq)| ≤
      |((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
        masterPrimePairDilationErrorCap (maskGeneratedMaster m gap) gap (maskOriginalPivotIndex C hC col) w| := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [maskStagePrimePairEta_dilation_bound S hS gap C hC hgap k col B] with w hb
  intro H hH
  rw [maskStageFreshOffDiagonalAverage_expectation, maskStageFreshOffDiagonalAverage_expectation]
  have he := expectation_difference_support_bound
    (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w))
    (tensor_nonneg _ _ (primePoolMass_nonneg _ _) (primePoolMass_nonneg _ _))
    (fun pq => if pq.1 ≠ pq.2 then
      maskStagePrimePairEtaAverage S hS gap C k col w pq.1 pq.2 (fun r => H r pq) else 0)
    (fun pq => if pq.1 ≠ pq.2 then
      maskStageCoordinateDilatedAverage S hS gap C k col w (pq.1*pq.2) (fun r => H r pq) else 0)
    |((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
      masterPrimePairDilationErrorCap (maskGeneratedMaster m gap) gap (maskOriginalPivotIndex C hC col) w|
    (fun pq hpq => by
      by_cases h : pq.1 ≠ pq.2
      · simp only [if_pos h]
        have hmem := Finset.mem_product.mp (tensor_support _ _ hpq)
        exact (hb pq.1 (primePoolMass_support _ _ hmem.1) pq.2
          (primePoolMass_support _ _ hmem.2) h (fun r => H r pq)
          (fun x hx z => hH x hx pq hpq z)).trans (le_abs_self _)
      · simp only [if_neg h, sub_self, abs_zero]
        exact abs_nonneg _)
  have ht : total (maskFreshPrimeMass (m := m) gap w) = 1 :=
    primePoolMass_total (hF.pool_positive_mass w (gap w).val)
  simpa only [tensor_total, ht, one_mul, maskStagePrimePairEtaAverage,
    maskStageCoordinateDilatedAverage] using he

include hC hgap in
theorem maskStageOffDiagonalAbsorption_uniform_zero (k : ℕ) (col : Fin (m + 1)) (B : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ H : MaskStagePoint S hS k → ℕ × ℕ → ℝ,
      (∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support,
        ∀ pq ∈ (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w)).support,
        ∀ z, |H (x,z) pq| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B) →
      |maskStageFreshOffDiagonalAverage S hS gap C k w
          (fun r pq => primeDivisorEta pq.1 (r.2 col) * primeDivisorEta pq.2 (r.2 col) * H r pq) -
        maskStageFreshOffDiagonalAverage S hS gap C k w
          (fun r pq => H (r.1, Function.update r.2 col (((pq.1*pq.2 : ℕ) : ℤ) * r.2 col)) pq)| < ε := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  have he : Tendsto (fun w => |((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
      masterPrimePairDilationErrorCap (maskGeneratedMaster m gap) gap (maskOriginalPivotIndex C hC col) w|)
      atTop (𝓝 0) := by
    simpa only [abs_zero] using (hF.prime_pair_dilation_weighted_cap_tendsto gap
      (maskOriginalPivotIndex C hC col) (hgap.mono (fun w hw => hw col)) B).abs
  filter_upwards [maskStageOffDiagonalAbsorption_bound S hS gap C hC hgap k col B,
    he.eventually (eventually_lt_nhds hε)] with w hb hew
  intro H hH
  exact (hb H hH).trans_lt hew

theorem maskStageBalancedBranches_dilated_eq (k : ℕ) (u v : Fin (m + 1)) (hne : u ≠ v) (w : ℕ)
    (H : MaskStagePoint S hS k → ℕ → ℝ) :
    maskStageFreshOffDiagonalAverage S hS gap C k w (fun r pq =>
      H (r.1, maskBalancedCoordinates u v pq.1
        (Function.update r.2 u (((pq.1*pq.2 : ℕ) : ℤ) * r.2 u))) pq.1 *
      H (r.1, maskBalancedCoordinates u v pq.2
        (Function.update r.2 u (((pq.1*pq.2 : ℕ) : ℤ) * r.2 u))) pq.2) =
      maskStageFreshOffDiagonalAverage S hS gap C k w (fun r pq =>
        H (r.1, maskAbsorbedCoordinates u v pq.1 pq.2 r.2) pq.1 *
        H (r.1, maskAbsorbedCoordinates u v pq.2 pq.1 r.2) pq.2) := by
  rw [maskStageFreshOffDiagonalAverage_expectation, maskStageFreshOffDiagonalAverage_expectation]
  apply expectation_congr_support
  intro pq hpq
  have hmem := Finset.mem_product.mp (tensor_support _ _ hpq)
  have hp := (primePool_mem.mp (primePoolMass_support _ _ hmem.1)).2.2.ne_zero
  have hq := (primePool_mem.mp (primePoolMass_support _ _ hmem.2)).2.2.ne_zero
  by_cases h : pq.1 ≠ pq.2
  · simp only [if_pos h]
    apply congrArg (expectation _)
    funext r
    rw [maskBalancedCoordinates_pair_dilation u v hne hp,
      maskBalancedCoordinates_pair_dilation_swapped u v hne pq.1 hq]
  · simp only [if_neg h]

include hC hgap in
theorem maskStageBalancedBranches_absorption_bound (k : ℕ) (u v : Fin (m + 1)) (hne : u ≠ v) (B : ℕ) :
    ∀ᶠ w in atTop, ∀ H : MaskStagePoint S hS k → ℕ → ℝ,
      (∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support,
        ∀ p ∈ (maskFreshPrimeMass (m := m) gap w).support,
        ∀ z, |H (x,z) p| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B) →
      |maskStageFreshOffDiagonalAverage S hS gap C k w (fun r pq =>
          primeDivisorEta pq.1 (r.2 u) * primeDivisorEta pq.2 (r.2 u) *
            (H (r.1, maskBalancedCoordinates u v pq.1 r.2) pq.1 *
              H (r.1, maskBalancedCoordinates u v pq.2 r.2) pq.2)) -
        maskStageFreshOffDiagonalAverage S hS gap C k w (fun r pq =>
          H (r.1, maskAbsorbedCoordinates u v pq.1 pq.2 r.2) pq.1 *
          H (r.1, maskAbsorbedCoordinates u v pq.2 pq.1 r.2) pq.2)| ≤
      |((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2*B) *
        masterPrimePairDilationErrorCap (maskGeneratedMaster m gap) gap (maskOriginalPivotIndex C hC u) w| := by
  filter_upwards [maskStageOffDiagonalAbsorption_bound S hS gap C hC hgap k u (2*B)] with w hb
  intro H hH
  have he := hb (fun r pq => H (r.1, maskBalancedCoordinates u v pq.1 r.2) pq.1 *
      H (r.1, maskBalancedCoordinates u v pq.2 r.2) pq.2) (fun x hx pq hpq z => by
    have hmem := Finset.mem_product.mp (tensor_support _ _ hpq)
    rw [abs_mul]
    calc
      _ ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B *
          ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B :=
        mul_le_mul (hH x hx pq.1 hmem.1 _) (hH x hx pq.2 hmem.2 _) (abs_nonneg _) (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega)
  rw [maskStageBalancedBranches_dilated_eq S hS gap C k u v hne w H] at he
  exact he

include hC hgap in
theorem maskStageBalancedBranches_absorption_uniform_zero (k : ℕ) (u v : Fin (m + 1))
    (hne : u ≠ v) (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ H : MaskStagePoint S hS k → ℕ → ℝ,
      (∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support,
        ∀ p ∈ (maskFreshPrimeMass (m := m) gap w).support,
        ∀ z, |H (x,z) p| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B) →
      |maskStageFreshOffDiagonalAverage S hS gap C k w (fun r pq =>
          primeDivisorEta pq.1 (r.2 u) * primeDivisorEta pq.2 (r.2 u) *
            (H (r.1, maskBalancedCoordinates u v pq.1 r.2) pq.1 *
              H (r.1, maskBalancedCoordinates u v pq.2 r.2) pq.2)) -
        maskStageFreshOffDiagonalAverage S hS gap C k w (fun r pq =>
          H (r.1, maskAbsorbedCoordinates u v pq.1 pq.2 r.2) pq.1 *
          H (r.1, maskAbsorbedCoordinates u v pq.2 pq.1 r.2) pq.2)| < ε := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  have he : Tendsto (fun w => |((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2*B) *
      masterPrimePairDilationErrorCap (maskGeneratedMaster m gap) gap (maskOriginalPivotIndex C hC u) w|)
      atTop (𝓝 0) := by
    simpa only [abs_zero] using (hF.prime_pair_dilation_weighted_cap_tendsto gap
      (maskOriginalPivotIndex C hC u) (hgap.mono (fun w hw => hw u)) (2*B)).abs
  filter_upwards [maskStageBalancedBranches_absorption_bound S hS gap C hC hgap k u v hne B,
    he.eventually (eventually_lt_nhds hε)] with w hb hew
  intro H hH
  exact (hb H hH).trans_lt hew

end Hindman168
