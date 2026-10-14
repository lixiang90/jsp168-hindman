import Hindman168.MaskCurrentNormalizedExtraction

/-! Admissible row/mask inputs at an actual prefix stage. Bounds are
required on old-prime-support tuples and every integer argument. The
original and normalized tests inherit a derived m-only polynomial cap. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (C : ℕ → Chain (m + 1))

structure MaskStageCorrelationInput (k w : ℕ) (T : Finset (Finset (Fin (m + 1)))) where
  rows : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) →
    Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ
  masks : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ
  row_bound : ∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support,
    ∀ i t, |rows x i t| ≤ maskStageRowMajorant S hS gap C k w i t
  mask_bound : ∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support,
    ∀ V ∈ T, ∀ t, |masks x V t| ≤ 1

noncomputable def maskStageInputTest {k w : ℕ} {T : Finset (Finset (Fin (m + 1)))}
    (D : MaskStageCorrelationInput S hS gap C k w T) (r : MaskStagePoint S hS k) : ℝ :=
  maskRowFunctionProduct (maskPrefixRowStage S hS k).rows
    (masterColumnCoefficient N a (fun w => (C w).block) w) D.rows r.1 r.2 *
  maskMultiplicativeProduct T D.masks r.1 r.2

noncomputable def maskStageInputCorrelation {k w : ℕ} {T : Finset (Finset (Fin (m + 1)))}
    (D : MaskStageCorrelationInput S hS gap C k w T) : ℝ :=
  maskRowMaskCorrelation gap C (maskPrefixRowStage S hS k).rows
    (masterColumnCoefficient N a (fun w => (C w).block) w) w T D.masks D.rows

noncomputable def maskStageNextInputCorrelation {k w : ℕ} {T : Finset (Finset (Fin (m + 1)))}
    (D : MaskStageCorrelationInput S hS gap C k w T) (U : Finset (Fin (m + 1))) : ℝ :=
  maskRowMaskCorrelation gap C ((maskPrefixRowStage S hS k).step hS U).rows
    (masterColumnCoefficient N a (fun w => (C w).block) w) w (T.erase U)
    (maskUpdatedMultiplicativeMasks (chosenMaskColumnPlan S U hS) D.masks)
    (maskUpdatedRowFunctions gap C (chosenMaskColumnPlan S U hS) (maskPrefixRowStage S hS k).rows w D.rows)

noncomputable def maskStageNormalizedInputTest {k w : ℕ} {T : Finset (Finset (Fin (m + 1)))}
    (D : MaskStageCorrelationInput S hS gap C k w T) (U : Finset (Fin (m + 1)))
    (r : MaskStagePoint S hS k) : ℝ :=
  maskStageNormalizedIntegrand S hS gap a C k U w (T.erase U) D.masks D.rows r.1 r.2

theorem maskStageOuterMass_support_old (k w : ℕ) (r : MaskStagePoint S hS k)
    (hr : r ∈ (maskStageOuterMass S hS gap C k w).support) :
    r.1 ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support := by
  apply Finsupp.mem_support_iff.mpr
  intro he
  have hn := Finsupp.mem_support_iff.mp hr
  rw [maskStageOuterMass, conditionalJoint_apply, he, zero_mul] at hn
  exact hn rfl

variable (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include hC in
theorem maskStageOuterMass_eventually_total_one :
    ∀ᶠ w in atTop, ∀ k, total (maskStageOuterMass S hS gap C k w) = 1 := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [base_probability_eventually gap C hC] with w hb
  intro k
  rw [maskStageOuterMass, conditionalJoint_total]
  simp only [hb.2, expectation_const, mul_one]
  exact hF.prime_slots_total w (fun _ : Fin (maskPrefixRowStage S hS k).primeArity => (gap w).val)

include hC htail in
theorem maskStageInputTest_eventually_polynomial_bound :
    ∀ᶠ w in atTop, ∀ k T (D : MaskStageCorrelationInput S hS gap C k w T),
      ∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support, ∀ z,
      |maskStageInputTest S hS gap a C D (x,z)| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m) := by
  filter_upwards [maskStageRowWeight_eventually_bounds S hS gap a C hC htail] with w hw
  intro k T D x hx z
  let V : ℝ := (maskGeneratedMaster m gap).auxiliary w (gap w).val
  have hV : 2 ≤ V := by
    dsimp [V]
    exact_mod_cast (maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val
  have hr : |maskRowFunctionProduct (maskPrefixRowStage S hS k).rows
      (masterColumnCoefficient N a (fun w => (C w).block) w) D.rows x z| ≤
      V ^ (2 * maskRowCountBound m) := by
    unfold maskRowFunctionProduct
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ i : Fin (maskPrefixRowStage S hS k).rowCount, V ^ 2 := by
        apply Finset.prod_le_prod
        · intro i _; exact abs_nonneg _
        · intro i _
          have hi := (hw k i x z).2
          have hf := D.row_bound x hx i ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
            (masterColumnCoefficient N a (fun w => (C w).block) w) i z)
          change monomialRowWeight gap a C (maskPrefixRowStage S hS k).rows
            (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id) w i x z ≤ V at hi
          change |D.rows x i _| ≤ 1 + monomialRowWeight gap a C (maskPrefixRowStage S hS k).rows
            (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id) w i x z at hf
          nlinarith
      _ = V ^ (2 * (maskPrefixRowStage S hS k).rowCount) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      _ ≤ V ^ (2 * maskRowCountBound m) :=
        pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_left 2 (maskPrefixRowStage_rowCount_le S hS k))
  unfold maskStageInputTest
  rw [abs_mul]
  simpa only [mul_one] using mul_le_mul hr
    (maskMultiplicativeProduct_bound T D.masks x (D.mask_bound x hx) z) (abs_nonneg _) (by positivity)

include hC htail in
theorem maskStageNormalizedInputTest_eventually_bound :
    ∀ᶠ w in atTop, ∀ k T (D : MaskStageCorrelationInput S hS gap C k w T) U,
      ∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support, ∀ z,
      |maskStageNormalizedInputTest S hS gap a C D U (x,z)| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m) := by
  filter_upwards [maskStageNormalizedIntegrand_eventually_bound S hS gap a C hC htail] with w hw
  intro k T D U x hx z
  exact hw k U (T.erase U) D.masks D.rows x
    (fun V hV => D.mask_bound x hx V (Finset.mem_of_mem_erase hV)) (D.row_bound x hx) z

include hC htail in
theorem maskStageInputCorrelation_eventually_polynomial_bound :
    ∀ᶠ w in atTop, ∀ k T (D : MaskStageCorrelationInput S hS gap C k w T),
      |maskStageInputCorrelation S hS gap a C D| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m) := by
  filter_upwards [maskStageInputTest_eventually_polynomial_bound S hS gap a C hC htail,
    maskStageOuterMass_eventually_nonneg S hS gap C hC,
    maskStageOuterMass_eventually_total_one S hS gap C hC] with w hb hn ht
  intro k T D
  unfold maskStageInputCorrelation
  rw [maskRowMaskCorrelation_originalOuter]
  have h := abs_expectation_le_majorant_support (maskStageOuterMass S hS gap C k w)
    (maskStageInputTest S hS gap a C D)
    (fun _ => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m))
    (hn k) (fun r hr => hb k T D r.1 (maskStageOuterMass_support_old S hS gap C k w r hr) r.2)
  rw [expectation_const, ht k, one_mul] at h
  exact h

end Hindman168
