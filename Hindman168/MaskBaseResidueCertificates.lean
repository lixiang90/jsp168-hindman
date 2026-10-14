import Hindman168.PolynomialNormalizedResidueMinors
import Hindman168.MaskTargetPolynomialBudgets
import Hindman168.PolynomialCopiedIntegerRows

/-! Base-row certificates on the whole original prime-pool support.
Primitivity needs no good event. Pair independence excludes only residues
of the unchanged fixed nonzero polynomial catalogue, prime by prime. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

include ha hC in
theorem maskGenerated_base_rows_primitive :
    ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass (maskGeneratedMaster m gap) w
      (fun _ : Fin (maskGeneratedRowDataFamily m gap t).arity => (gap w).val)).support,
      ∀ p : boundedRoughPrimeSet w ((maskGeneratedMaster m gap).auxiliary w (gap w).val),
      ∀ i, ∃ j, ((maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerRow x
        (masterColumnCoefficient N a (fun w => (C w).block) w) i j : ZMod (p : ℕ)) ≠ 0 := by
  filter_upwards [maskGenerated_chain_integer_anchor_units m gap a ha C hC] with w hu
  intro x hx p i
  have hp := (mem_boundedRoughPrimeSet w ((maskGeneratedMaster m gap).auxiliary w (gap w).val) (p : ℕ)).mp p.property
  letI : Fact (p : ℕ).Prime := ⟨hp.1⟩
  refine ⟨(maskGeneratedRowDataFamily m gap t).rows.normalizationAnchor i, ?_⟩
  exact (hu t x hx i (p : ℕ) hp.1.pos hp.2.2).ne_zero

include ha hC in
theorem maskGenerated_base_rows_independent :
    ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass (maskGeneratedMaster m gap) w
      (fun _ : Fin (maskGeneratedRowDataFamily m gap t).arity => (gap w).val)).support,
      ∀ p : boundedRoughPrimeSet w ((maskGeneratedMaster m gap).auxiliary w (gap w).val),
      ¬ squarefreeCRTBadEvent
        (boundedRoughPrimeSet w ((maskGeneratedMaster m gap).auxiliary w (gap w).val))
        (fun p hp => ((mem_boundedRoughPrimeSet w ((maskGeneratedMaster m gap).auxiliary w (gap w).val) p).mp hp).1)
        ((maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target)
        (fun j => (x j : ZMod (squarefreeCRTModulus
          (boundedRoughPrimeSet w ((maskGeneratedMaster m gap).auxiliary w (gap w).val))))) p →
      ∀ i l, i ≠ l → LinearIndependent (ZMod (p : ℕ))
        ![(fun j => ((maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerRow x
          (masterColumnCoefficient N a (fun w => (C w).block) w) i j : ZMod (p : ℕ))),
          (fun j => ((maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerRow x
          (masterColumnCoefficient N a (fun w => (C w).block) w) l j : ZMod (p : ℕ)))] := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [maskGenerated_chain_integer_row_conditions m gap a ha C hC,
    MaskOriginalSampling.actualColumnBounds_eventually (m := m) gap a ha C hC] with w hr hc
  intro x _ p hbad i l hil
  have hp := (mem_boundedRoughPrimeSet w ((maskGeneratedMaster m gap).auxiliary w (gap w).val) (p : ℕ)).mp p.property
  apply (hr t x).residue_pair_independent (fun col => (hc col).1)
    (maskGeneratedRowDataFamily m gap t).target i l hil (p : ℕ) hp.1
  · intro col
    exact natDivisor_residue_isUnit (hc col).2.1
      (hF.modulus_residue_isUnit w (p : ℕ) (prime_coprime_primorial_of_gt hp.1 hp.2.1).symm)
  · exact (maskGeneratedRowDataFamily m gap t).rows.catalog_nonzero_of_not_squarefree_bad _ _ _ x p hbad

end Hindman168
