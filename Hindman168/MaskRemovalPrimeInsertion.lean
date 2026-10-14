import Hindman168.MasterPrimeAverageInsertion
import Hindman168.MaskRemovalStageDiagonal

/-! Prime insertion on every actual intermediate mask old-prime/base
law. One original harmonic coordinate is extracted exactly; the old
prime tuple and all other coordinates form the independent outside law.
No abstract vanishing-error premise or numerical good event is added. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

namespace FiniteMass

theorem update_insertPivotCoordinate {ι α : Type*} [DecidableEq ι] (k : ι)
    (rest : {i : ι // i ≠ k} → α) (x y : α) :
    Function.update (insertPivotCoordinate k rest x) k y = insertPivotCoordinate k rest y := by
  funext i
  by_cases hi : i = k
  · subst i
    simp only [Function.update_self, insertPivotCoordinate_self]
  · simp [Function.update, insertPivotCoordinate, hi]

end FiniteMass

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

abbrev MaskInsertionOutsidePoint (k : ℕ) (col : Fin (m + 1)) :=
  (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) × ({j : Fin (m + 1) // j ≠ col} → ℤ)

noncomputable def maskStagePrimeInsertionOutsideMass (k : ℕ) (col : Fin (m + 1)) (w : ℕ) :
    Mass (MaskInsertionOutsidePoint S hS k col) :=
  tensor (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w)
    (piMass (fun j : {j : Fin (m + 1) // j ≠ col} =>
      integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot j.val)) (primorial w)))

noncomputable def maskStagePivotTest (k : ℕ) (col : Fin (m + 1))
    (H : MaskStagePoint S hS k → ℝ) (r : MaskInsertionOutsidePoint S hS k col) (z : ℤ) : ℝ :=
  H (r.1, insertPivotCoordinate col r.2 z)

noncomputable def maskStagePrimeInsertedAverage (k : ℕ) (col : Fin (m + 1)) (w : ℕ)
    (H : MaskStagePoint S hS k → ℝ) : ℝ :=
  expectation (maskStageOuterMass S hS gap C k w) (fun r =>
    expectation (maskFreshPrimeMass (m := m) gap w)
      (fun p => H (r.1, Function.update r.2 col ((p : ℤ) * r.2 col))))

theorem maskStageAverage_pivot (k : ℕ) (col : Fin (m + 1)) (w : ℕ)
    (H : MaskStagePoint S hS k → ℝ) :
    expectation (maskStageOuterMass S hS gap C k w) H =
      expectation (maskStagePrimeInsertionOutsideMass S hS gap C k col w) (fun r =>
        expectation (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
          (maskStagePivotTest S hS k col H r)) := by
  unfold maskStageOuterMass
  rw [expectation_conditionalJoint]
  simp_rw [maskOriginalBaseMass, expectation_piMass_pivot _ col]
  unfold maskStagePrimeInsertionOutsideMass maskStagePivotTest
  rw [expectation_tensor]
  congr 1
  funext x
  congr 1
  exact congrArg (fun inst : Fintype {j : Fin (m + 1) // j ≠ col} =>
    @piMass _ inst (fun _ => ℤ) (fun j =>
      integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot j.val)) (primorial w)))
    (Subsingleton.elim _ _)

theorem maskStagePrimeInsertedAverage_pivot (k : ℕ) (col : Fin (m + 1)) (w : ℕ)
    (H : MaskStagePoint S hS k → ℝ) :
    maskStagePrimeInsertedAverage S hS gap C k col w H =
      expectation (maskStagePrimeInsertionOutsideMass S hS gap C k col w) (fun r =>
        expectation (maskFreshPrimeMass (m := m) gap w) (fun p =>
          expectation (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
            (fun z => maskStagePivotTest S hS k col H r ((p : ℤ) * z)))) := by
  unfold maskStagePrimeInsertedAverage maskStageOuterMass
  rw [expectation_conditionalJoint]
  simp_rw [maskOriginalBaseMass, expectation_piMass_pivot _ col]
  simp only [insertPivotCoordinate_self, update_insertPivotCoordinate]
  simp_rw [expectation_comm (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col))
    (primorial w)) (maskFreshPrimeMass (m := m) gap w)]
  unfold maskStagePrimeInsertionOutsideMass maskStagePivotTest
  rw [expectation_tensor]
  congr 1
  funext x
  congr 1
  exact congrArg (fun inst : Fintype {j : Fin (m + 1) // j ≠ col} =>
    @piMass _ inst (fun _ => ℤ) (fun j =>
      integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot j.val)) (primorial w)))
    (Subsingleton.elim _ _)

include hC in
theorem maskStagePrimeInsertionOutsideMass_eventually_probability :
    ∀ᶠ w in atTop, ∀ k col,
      (∀ r, 0 ≤ maskStagePrimeInsertionOutsideMass S hS gap C k col w r) ∧
        total (maskStagePrimeInsertionOutsideMass S hS gap C k col w) = 1 := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.raw_cutoffs_valid] with w hv
  have hZ (col : Fin (m + 1)) : 0 < harmonicNormalizer
      ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w) :=
    (hv _ (hC w col (by simp [Chain.block]))).2.2
  intro k col
  unfold maskStagePrimeInsertionOutsideMass
  constructor
  · exact tensor_nonneg _ _ (hF.prime_slots_nonneg w (fun _ => (gap w).val))
      (piMass_nonneg _ (fun j z => integerMass_nonneg (hZ j.val) z))
  · rw [tensor_total]
    have ht : total (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w) = 1 :=
      hF.prime_slots_total w (fun _ => (gap w).val)
    rw [ht, one_mul]
    exact piMass_total_one _ (fun j => integerMass_total (hZ j.val))

include hC hgap in
theorem maskStagePrimeInsertion_bound (k : ℕ) (col : Fin (m + 1)) (B : ℕ) :
    ∀ᶠ w in atTop, ∀ H : MaskStagePoint S hS k → ℝ,
      (∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support,
        ∀ z, |H (x,z)| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B) →
      |expectation (maskStageOuterMass S hS gap C k w) H -
        maskStagePrimeInsertedAverage S hS gap C k col w H| ≤
      masterPrimeInsertionErrorCap (maskGeneratedMaster m gap) gap (maskOriginalPivotIndex C hC col) B w := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.prime_average_insertion_outside_bound (ι := MaskInsertionOutsidePoint S hS k col)
    gap (maskOriginalPivotIndex C hC col) (hgap.mono (fun w hw => hw col)) B,
    maskStagePrimeInsertionOutsideMass_eventually_probability S hS gap C hC] with w hb hprob
  intro H hH
  rw [maskStageAverage_pivot, maskStagePrimeInsertedAverage_pivot]
  apply hb _ (hprob k col).1 (hprob k col).2
  intro r hr z
  have hx := (Finset.mem_product.mp (tensor_support _ _ hr)).1
  exact hH r.1 hx _

include hC hgap in
theorem maskStagePrimeInsertion_uniform_zero (k : ℕ) (col : Fin (m + 1)) (B : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ H : MaskStagePoint S hS k → ℝ,
      (∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support,
        ∀ z, |H (x,z)| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B) →
      |expectation (maskStageOuterMass S hS gap C k w) H -
        maskStagePrimeInsertedAverage S hS gap C k col w H| < ε := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [maskStagePrimeInsertion_bound S hS gap C hC hgap k col B,
    (hF.prime_insertion_error_cap_tendsto gap (maskOriginalPivotIndex C hC col)
      (hgap.mono (fun w hw => hw col)) B).eventually (eventually_lt_nhds hε)] with w hb he
  intro H hH
  exact (hb H hH).trans_lt he

end Hindman168
