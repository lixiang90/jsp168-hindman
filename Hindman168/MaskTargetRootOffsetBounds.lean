import Hindman168.MaskTargetPolynomialBudgets

/-! Uniform affine offset bound on original harmonic and quotient-pair
supports. The original remaining coordinates are kept, including all zero
columns above the maximum support anchor. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def targetRootOffsetCap (w : ℕ) : ℕ :=
  (m + 1) * ((maskGeneratedMaster m gap).auxiliary w (gap w).val *
    rootPoolBudget (m := m) gap w ^ targetRootRowExponent gap t *
    (maskGeneratedMaster m gap).auxiliary w ((C w).pivot (targetRootAnchor gap t))) +
  Fintype.card (MaskOriginalDirection m gap t) *
    ((maskGeneratedMaster m gap).auxiliary w (gap w).val *
      rootPoolBudget (m := m) gap w ^ targetRootDenExponent gap t) *
    (maskGeneratedMaster m gap).gap w (gap w).val

theorem directionPair_support_first_le_gap (J w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (v : MaskOriginalDirection m gap t → ℤ × ℤ)
    (hv : v ∈ (MaskRootOriginalSampling.directionPairMass gap t J w x).support) (k : MaskOriginalDirection m gap t) :
    (v k).1.natAbs ≤ (maskGeneratedMaster m gap).gap w (gap w).val := by
  have hk := piMass_mem_support_coordinate _ v hv k
  have hb := uniformIntervalMass_support_bounds 0 (maskGeneratedShiftLength m gap t J w x)
    (Finset.mem_product.mp (tensor_support _ _ hk)).1
  have he : ((v k).1.natAbs : ℤ) ≤ maskGeneratedShiftLength m gap t J w x := by
    rw [Int.natCast_natAbs, abs_of_nonneg hb.1]
    simpa only [zero_add] using hb.2.le
  have hn : (v k).1.natAbs ≤ maskGeneratedShiftLength m gap t J w x := by exact_mod_cast he
  exact hn.trans (Nat.div_le_self _ _)

theorem directionPair_first_sum_natAbs_le_gap (J w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (v : MaskOriginalDirection m gap t → ℤ × ℤ)
    (hv : v ∈ (MaskRootOriginalSampling.directionPairMass gap t J w x).support) :
    (∑ k, (v k).1).natAbs ≤ Fintype.card (MaskOriginalDirection m gap t) *
      (maskGeneratedMaster m gap).gap w (gap w).val := by
  calc
    _ ≤ ∑ k, (v k).1.natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _k : MaskOriginalDirection m gap t, (maskGeneratedMaster m gap).gap w (gap w).val :=
      Finset.sum_le_sum (fun k _ => directionPair_support_first_le_gap gap t J w x v hv k)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ]; rfl

include ha hC in
theorem targetRootOffset_supported_bound (J : ℕ) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ rest v,
      rest ∈ (rootRestMass gap C t w).support →
      v ∈ (MaskRootOriginalSampling.directionPairMass gap t J w x).support →
      (targetRootOffset gap a C t w x rest v).natAbs ≤ targetRootOffsetCap gap C t w := by
  filter_upwards [actualColumnBounds_eventually (m := m) gap a ha C hC] with w hc
  intro x hx rest v hr hv
  have hrest := (maskGeneratedRowDataFamily m gap t).rows.normalizedRootOffset_size_bound x
    (masterColumnCoefficient N a (fun w => (C w).block) w) _ rest
    (rootPoolBudget_ge_two gap w) (rootPoolBudget_supported_primes gap t w x hx)
    (fun col => (hc col).2.2) (rootRestMass_support_before_anchor gap C t w rest hr)
  have hdir := directionPair_first_sum_natAbs_le_gap gap t J w x v hv
  have hmod := targetRootTranslationModulus_bound gap t w x hx
  unfold targetRootOffset targetRootOffsetCap
  calc
    _ ≤ _ := Int.natAbs_add_le _ _
    _ ≤ _ := add_le_add hrest (by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      have he := Nat.mul_le_mul hmod hdir
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using he)

end Hindman168.MaskOriginalSampling
