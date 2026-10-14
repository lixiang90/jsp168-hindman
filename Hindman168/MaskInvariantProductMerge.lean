import Hindman168.MaskMergedInvariantFunctions

/-! Actual invariant-row products after the two absorbed branches.
Their normalized branch factors combine with exactly one invariant
row density Omega into the product of the bounded merged row functions. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

noncomputable def maskStageInvariantRatioProduct (k : ℕ) (U : Finset (Fin (m + 1))) (w : ℕ)
    (f : Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ)
    (x : Fin (maskPrefixRowStage S hS k).primeArity → ℕ) (z : Fin (m + 1) → ℤ) : ℝ :=
  ∏ i ∈ maskStageInvariantRows S hS k U,
    f i ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
      (masterColumnCoefficient N a (fun w => (C w).block) w) i z) /
    maskStageRowMajorant S hS gap C k w i
      ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
        (masterColumnCoefficient N a (fun w => (C w).block) w) i z)

noncomputable def maskStageInvariantMergedProduct (k : ℕ) (U : Finset (Fin (m + 1)))
    (w p q : ℕ) (f g : Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ)
    (x : Fin (maskPrefixRowStage S hS k).primeArity → ℕ) (z : Fin (m + 1) → ℤ) : ℝ :=
  ∏ i ∈ maskStageInvariantRows S hS k U,
    maskStageInvariantMergedFunction S hS gap C k U w p q i (f i) (g i)
      ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
        (masterColumnCoefficient N a (fun w => (C w).block) w) i z)

theorem maskStageDensity_eq_product_majorants (k : ℕ) (U : Finset (Fin (m + 1))) (w : ℕ)
    (x : Fin (maskPrefixRowStage S hS k).primeArity → ℕ) (z : Fin (m + 1) → ℤ) :
    maskStageDensity S hS gap a C k U w (x, z) =
      ∏ i ∈ maskStageInvariantRows S hS k U, maskStageRowMajorant S hS gap C k w i
        ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
          (masterColumnCoefficient N a (fun w => (C w).block) w) i z) := rfl

include hC in
theorem maskStageInvariantRatioProduct_eventually_bound :
    ∀ᶠ w in atTop, ∀ k U,
      ∀ f : Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ,
      (∀ i ∈ maskStageInvariantRows S hS k U, ∀ t,
        |f i t| ≤ maskStageRowMajorant S hS gap C k w i t) → ∀ x z,
      |maskStageInvariantRatioProduct S hS gap a C k U w f x z| ≤ 1 := by
  filter_upwards [maskStageRowMajorant_eventually_positive S hS gap C hC] with w hw
  intro k U f hf x z
  unfold maskStageInvariantRatioProduct
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ i ∈ maskStageInvariantRows S hS k U, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i _
        exact abs_nonneg _
      · intro i hi
        rw [abs_div, abs_of_pos (hw k i _)]
        apply (div_le_iff₀ (hw k i _)).mpr
        simpa only [one_mul] using hf i hi _
    _ = 1 := by simp

include hC htail in
theorem maskStageInvariantRatioProduct_eventually_absorbed :
    ∀ᶠ w in atTop, ∀ k U,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ f : Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ, ∀ x z,
      maskStageInvariantRatioProduct S hS gap a C k U w f x
        ((chosenMaskColumnPlan S U hS).absorbedCoordinates p q z) =
      ∏ i ∈ maskStageInvariantRows S hS k U,
        f i ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
          (masterColumnCoefficient N a (fun w => (C w).block) w) i
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates p q z)) /
        maskStageRowMajorant S hS gap C k w i
          ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
            (masterColumnCoefficient N a (fun w => (C w).block) w) i z) := by
  filter_upwards [maskStageInvariantWeight_absorbed S hS gap a C hC htail] with w hw
  intro k U p hp q hq f x z
  unfold maskStageInvariantRatioProduct
  apply Finset.prod_congr rfl
  intro i hi
  have hW := congrArg (fun v : ℝ => 1 + v) (hw k U i hi p hp q hq x z)
  change maskStageRowMajorant S hS gap C k w i
    ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
      (masterColumnCoefficient N a (fun w => (C w).block) w) i
      ((chosenMaskColumnPlan S U hS).absorbedCoordinates p q z)) =
    maskStageRowMajorant S hS gap C k w i
      ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
        (masterColumnCoefficient N a (fun w => (C w).block) w) i z) at hW
  rw [hW]

include hC htail in
theorem maskStageInvariantMergedProduct_eventually_bound :
    ∀ᶠ w in atTop, ∀ k U,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ f g : Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ,
      (∀ i ∈ maskStageInvariantRows S hS k U, ∀ t,
        |f i t| ≤ maskStageRowMajorant S hS gap C k w i t) →
      (∀ i ∈ maskStageInvariantRows S hS k U, ∀ t,
        |g i t| ≤ maskStageRowMajorant S hS gap C k w i t) → ∀ x z,
      |maskStageInvariantMergedProduct S hS gap a C k U w p q f g x z| ≤
        maskStageDensity S hS gap a C k U w (x, z) := by
  filter_upwards [maskStageInvariantMergedFunction_eventually_bound S hS gap C hC htail] with w hw
  intro k U p hp q hq f g hf hg x z
  rw [maskStageDensity_eq_product_majorants]
  unfold maskStageInvariantMergedProduct
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _
    exact abs_nonneg _
  · intro i hi
    exact hw k U i p hp q hq (f i) (g i) (hf i hi) (hg i hi) _

include hC htail in
theorem maskStageInvariantProducts_eventually_merge :
    ∀ᶠ w in atTop, ∀ k U,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ f g : Fin (maskPrefixRowStage S hS k).rowCount → ℤ → ℝ, ∀ x z,
      maskStageDensity S hS gap a C k U w (x, z) *
        maskStageInvariantRatioProduct S hS gap a C k U w f x
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates p q z) *
        maskStageInvariantRatioProduct S hS gap a C k U w g x
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates q p z) =
      maskStageInvariantMergedProduct S hS gap a C k U w p q f g x z := by
  filter_upwards [maskStageInvariantRatioProduct_eventually_absorbed S hS gap a C hC htail,
    maskStageInvariantMergedFunction_eventually_factorization S hS gap C hC a,
    maskStageRowMajorant_eventually_positive S hS gap C hC] with w ha hf hn
  intro k U p hp q hq f g x z
  rw [ha k U p hp q hq f x z, ha k U q hq p hp g x z,
    maskStageDensity_eq_product_majorants, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  unfold maskStageInvariantMergedProduct
  apply Finset.prod_congr rfl
  intro i hi
  have hW := hn k i ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
    (masterColumnCoefficient N a (fun w => (C w).block) w) i z)
  have he := hf k U i hi p q (f i) (g i) x z
  calc
    _ = (f i ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
          (masterColumnCoefficient N a (fun w => (C w).block) w) i
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates p q z)) *
        g i ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
          (masterColumnCoefficient N a (fun w => (C w).block) w) i
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates q p z))) /
        maskStageRowMajorant S hS gap C k w i
          ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
            (masterColumnCoefficient N a (fun w => (C w).block) w) i z) := by
      field_simp
    _ = _ := by
      symm
      apply (eq_div_iff hW.ne').mpr
      simpa only [mul_comm] using he

end Hindman168
