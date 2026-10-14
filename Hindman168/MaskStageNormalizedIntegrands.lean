import Hindman168.MaskUpdatedRowProducts
import Hindman168.MaskUpdatedMultiplicativeMasks
import Hindman168.MaskRemovalStageDivisorCaps

/-! Concrete normalized tests in the paper's weighted mask square.
All bounds apply at every integer coordinate, and the absorbed double
branch is exactly the next-stage row/mask product. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

theorem maskInvariantFunctionProduct_stage (k : ℕ) (U : Finset (Fin (m + 1))) (w : ℕ)
    (f : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) →
      Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ)
    (x : Fin (maskPrefixRowStage S hS k).primeArity → ℕ) (z : Fin (m + 1) → ℤ) :
    maskInvariantFunctionProduct (maskPrefixRowStage S hS k).rows
      (chosenMaskColumnPlan S U hS).tag (masterColumnCoefficient N a (fun w => (C w).block) w) f x z =
      ∏ i ∈ maskStageInvariantRows S hS k U,
        f x i ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
          (masterColumnCoefficient N a (fun w => (C w).block) w) i z) := by
  unfold maskInvariantFunctionProduct
  exact (Finset.prod_subtype (F := (inferInstance : Fintype
    (MaskInvariantRowIndex (maskPrefixRowStage S hS k).rows (chosenMaskColumnPlan S U hS).tag)))
    (maskStageInvariantRows S hS k U) (by intro i; simp [maskStageInvariantRows])
    (fun i => f x i ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
      (masterColumnCoefficient N a (fun w => (C w).block) w) i z))).symm

theorem maskMergedFunctionProduct_stage (k : ℕ) (U : Finset (Fin (m + 1))) (w p q : ℕ)
    (f : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) →
      Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ)
    (x : Fin (maskPrefixRowStage S hS k).primeArity → ℕ) (z : Fin (m + 1) → ℤ) :
    maskMergedFunctionProduct gap C (chosenMaskColumnPlan S U hS) (maskPrefixRowStage S hS k).rows
      w p q (masterColumnCoefficient N a (fun w => (C w).block) w) f x z =
      maskStageInvariantMergedProduct S hS gap a C k U w p q (f x) (f x) x z := by
  unfold maskMergedFunctionProduct maskStageInvariantMergedProduct
  exact (Finset.prod_subtype (F := (inferInstance : Fintype
    (MaskInvariantRowIndex (maskPrefixRowStage S hS k).rows (chosenMaskColumnPlan S U hS).tag)))
    (maskStageInvariantRows S hS k U) (by intro i; simp [maskStageInvariantRows])
    (fun i => maskStageInvariantMergedFunction S hS gap C k U w p q i (f x i) (f x i)
      ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
        (masterColumnCoefficient N a (fun w => (C w).block) w) i z))).symm

noncomputable def maskStageNormalizedIntegrand (k : ℕ) (U : Finset (Fin (m + 1))) (w : ℕ)
    (T : Finset (Finset (Fin (m + 1))))
    (b : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ)
    (f : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) →
      Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ)
    (x : Fin (maskPrefixRowStage S hS k).primeArity → ℕ) (z : Fin (m + 1) → ℤ) : ℝ :=
  maskStageInvariantRatioProduct S hS gap a C k U w (f x) x z *
    maskNoninvariantFunctionProduct (maskPrefixRowStage S hS k).rows (chosenMaskColumnPlan S U hS).tag
      (masterColumnCoefficient N a (fun w => (C w).block) w) f x z *
    maskMultiplicativeProduct T b x z

include hC in
theorem maskStageNormalizedIntegrand_eventually_factorization :
    ∀ᶠ w in atTop, ∀ k U T,
      ∀ b : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ,
      ∀ f : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) →
        Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ, ∀ x z,
      maskStageDensity S hS gap a C k U w (x,z) *
        maskStageNormalizedIntegrand S hS gap a C k U w T b f x z =
      maskRowFunctionProduct (maskPrefixRowStage S hS k).rows
        (masterColumnCoefficient N a (fun w => (C w).block) w) f x z *
        maskMultiplicativeProduct T b x z := by
  filter_upwards [maskStageRowMajorant_eventually_positive S hS gap C hC] with w hw
  intro k U T b f x z
  have he : maskStageDensity S hS gap a C k U w (x,z) *
      maskStageInvariantRatioProduct S hS gap a C k U w (f x) x z =
      maskInvariantFunctionProduct (maskPrefixRowStage S hS k).rows
        (chosenMaskColumnPlan S U hS).tag (masterColumnCoefficient N a (fun w => (C w).block) w) f x z := by
    rw [maskStageDensity_eq_product_majorants, maskInvariantFunctionProduct_stage]
    unfold maskStageInvariantRatioProduct
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact mul_div_cancel₀ _ (hw k i _).ne'
  unfold maskStageNormalizedIntegrand
  rw [← mul_assoc, ← mul_assoc, he, ← maskRowFunctionProduct_split]

include hC htail in
theorem maskStageNoninvariantProduct_eventually_bound :
    ∀ᶠ w in atTop, ∀ k U,
      ∀ f : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) →
        Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ, ∀ x,
      (∀ i t, |f x i t| ≤ maskStageRowMajorant S hS gap C k w i t) → ∀ z,
      |maskNoninvariantFunctionProduct (maskPrefixRowStage S hS k).rows
        (chosenMaskColumnPlan S U hS).tag (masterColumnCoefficient N a (fun w => (C w).block) w) f x z| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m) := by
  filter_upwards [maskStageRowWeight_eventually_bounds S hS gap a C hC htail] with w hw
  intro k U f x hf z
  let V : ℝ := (maskGeneratedMaster m gap).auxiliary w (gap w).val
  have hV : 2 ≤ V := by
    dsimp [V]
    exact_mod_cast (maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val
  let J := Finset.univ.filter (fun i => ¬ maskRowInvariant
    ((maskPrefixRowStage S hS k).rows.row i) (chosenMaskColumnPlan S U hS).tag)
  have hc : J.card ≤ maskRowCountBound m :=
    (Finset.card_le_univ _).trans (by simpa using maskPrefixRowStage_rowCount_le S hS k)
  have he := Finset.prod_subtype (p := fun i => ¬ maskRowInvariant
    ((maskPrefixRowStage S hS k).rows.row i) (chosenMaskColumnPlan S U hS).tag)
    (F := (inferInstance : Fintype (MaskNoninvariantRowIndex (maskPrefixRowStage S hS k).rows
      (chosenMaskColumnPlan S U hS).tag))) J (by intro i; simp [J])
    (fun i => f x i ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
      (masterColumnCoefficient N a (fun w => (C w).block) w) i z))
  unfold maskNoninvariantFunctionProduct
  rw [← he, Finset.abs_prod]
  calc
    _ ≤ ∏ i ∈ J, V ^ 2 := by
      apply Finset.prod_le_prod
      · intro i _; exact abs_nonneg _
      · intro i _
        have hfi := hf i ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
          (masterColumnCoefficient N a (fun w => (C w).block) w) i z)
        have hi := (hw k i x z).2
        change monomialRowWeight gap a C (maskPrefixRowStage S hS k).rows
          (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id)
          w i x z ≤ V at hi
        change |f x i _| ≤ 1 + monomialRowWeight gap a C (maskPrefixRowStage S hS k).rows
          (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id)
          w i x z at hfi
        nlinarith
    _ = V ^ (2 * J.card) := by rw [Finset.prod_const, ← pow_mul]
    _ ≤ V ^ (2 * maskRowCountBound m) := pow_le_pow_right₀ (by linarith) (by omega)

include hC htail in
theorem maskStageNormalizedIntegrand_eventually_bound :
    ∀ᶠ w in atTop, ∀ k U T,
      ∀ b : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ,
      ∀ f : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) →
        Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ, ∀ x,
      (∀ V ∈ T, ∀ t, |b x V t| ≤ 1) →
      (∀ i t, |f x i t| ≤ maskStageRowMajorant S hS gap C k w i t) → ∀ z,
      |maskStageNormalizedIntegrand S hS gap a C k U w T b f x z| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m) := by
  filter_upwards [maskStageInvariantRatioProduct_eventually_bound S hS gap a C hC,
    maskStageNoninvariantProduct_eventually_bound S hS gap a C hC htail] with w hi hn
  intro k U T b f x hb hf z
  have h1 := hi k U (f x) (fun i _ => hf i) x z
  have h2 := hn k U f x hf z
  have h3 := maskMultiplicativeProduct_bound T b x hb z
  unfold maskStageNormalizedIntegrand
  rw [abs_mul, abs_mul]
  calc
    _ ≤ 1 * (((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m)) * 1 :=
      mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one) h3 (abs_nonneg _) (by positivity)
    _ = _ := by ring

include hC htail in
theorem maskStageNormalizedIntegrand_eventually_absorbed_update :
    ∀ᶠ w in atTop, ∀ k U T,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ b : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ,
      ∀ f : (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) →
        Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ, ∀ x z,
      maskStageDensity S hS gap a C k U w
        (x, (chosenMaskColumnPlan S U hS).absorptionCoordinates p q z) *
        maskStageNormalizedIntegrand S hS gap a C k U w T b f x
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates p q z) *
        maskStageNormalizedIntegrand S hS gap a C k U w T b f x
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates q p z) =
      maskRowFunctionProduct ((maskPrefixRowStage S hS k).step hS U).rows
        (masterColumnCoefficient N a (fun w => (C w).block) w)
        (maskUpdatedRowFunctions gap C (chosenMaskColumnPlan S U hS) (maskPrefixRowStage S hS k).rows w f)
        (maskFreshTuple x ((chosenMaskColumnPlan S U hS).freshValues p q)) z *
      maskMultiplicativeProduct T (maskUpdatedMultiplicativeMasks (chosenMaskColumnPlan S U hS) b)
        (maskFreshTuple x ((chosenMaskColumnPlan S U hS).freshValues p q)) z := by
  filter_upwards [maskStageInvariantProducts_eventually_absorptionMerge S hS gap a C hC htail] with w hm
  intro k U T p hp q hq b f x z
  dsimp only [TargetedMaskRowStage.step]
  rw [maskUpdatedRowProducts_join, maskMergedFunctionProduct_stage, maskMultiplicativeProduct_update]
  have he := hm k U p hp q hq (f x) (f x) x z
  unfold maskStageNormalizedIntegrand
  calc
    _ = (maskStageDensity S hS gap a C k U w
        (x, (chosenMaskColumnPlan S U hS).absorptionCoordinates p q z) *
        maskStageInvariantRatioProduct S hS gap a C k U w (f x) x
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates p q z) *
        maskStageInvariantRatioProduct S hS gap a C k U w (f x) x
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates q p z)) *
        (maskNoninvariantFunctionProduct (maskPrefixRowStage S hS k).rows
          (chosenMaskColumnPlan S U hS).tag (masterColumnCoefficient N a (fun w => (C w).block) w) f x
            ((chosenMaskColumnPlan S U hS).absorbedCoordinates p q z) *
         maskNoninvariantFunctionProduct (maskPrefixRowStage S hS k).rows
          (chosenMaskColumnPlan S U hS).tag (masterColumnCoefficient N a (fun w => (C w).block) w) f x
            ((chosenMaskColumnPlan S U hS).absorbedCoordinates q p z)) *
        (maskMultiplicativeProduct T b x ((chosenMaskColumnPlan S U hS).absorbedCoordinates p q z) *
         maskMultiplicativeProduct T b x ((chosenMaskColumnPlan S U hS).absorbedCoordinates q p z)) := by ring
    _ = _ := by rw [he]; ring

end Hindman168
