import Hindman168.MaskRemovalInvariantWeights

/-! Globally bounded merged functions for the original divisor majorant.
The scalar invariances hold on all integer arguments, so the displayed
quotient already supplies the paper's bounded extension everywhere. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

noncomputable def divisorWeightedMerge (ρ : Mass ℕ) (α β : ℕ) (f g : ℤ → ℝ) (t : ℤ) : ℝ :=
  f ((α : ℤ) * t) * g ((β : ℤ) * t) / (1 + integerDivisorMask ρ t)

theorem integerDivisorMask_nonneg_of_mass_nonneg (ρ : Mass ℕ) (hρ : ∀ d, 0 ≤ ρ d) (t : ℤ) :
    0 ≤ integerDivisorMask ρ t := by
  unfold integerDivisorMask
  apply Finset.sum_nonneg
  intro d _
  apply mul_nonneg (hρ d)
  split_ifs <;> positivity

theorem divisorWeightedMerge_bound (ρ : Mass ℕ) (hρ : ∀ d, 0 ≤ ρ d) (α β : ℕ)
    (hα : ∀ d ∈ ρ.support, α.Coprime d) (hβ : ∀ d ∈ ρ.support, β.Coprime d)
    (f g : ℤ → ℝ) (hf : ∀ t, |f t| ≤ 1 + integerDivisorMask ρ t)
    (hg : ∀ t, |g t| ≤ 1 + integerDivisorMask ρ t) (t : ℤ) :
    |divisorWeightedMerge ρ α β f g t| ≤ 1 + integerDivisorMask ρ t := by
  have hW : 0 < 1 + integerDivisorMask ρ t := by
    have h := integerDivisorMask_nonneg_of_mass_nonneg ρ hρ t
    linarith
  have hf' := hf ((α : ℤ) * t)
  have hg' := hg ((β : ℤ) * t)
  rw [integerDivisorMask_unit_scaled ρ α t hα] at hf'
  rw [integerDivisorMask_unit_scaled ρ β t hβ] at hg'
  unfold divisorWeightedMerge
  rw [abs_div, abs_mul, abs_of_pos hW]
  apply (div_le_iff₀ hW).mpr
  exact mul_le_mul hf' hg' (abs_nonneg _) hW.le

theorem divisorWeightedMerge_factorization (ρ : Mass ℕ) (hρ : ∀ d, 0 ≤ ρ d)
    (α β : ℕ) (f g : ℤ → ℝ) (t : ℤ) :
    (1 + integerDivisorMask ρ t) * divisorWeightedMerge ρ α β f g t =
      f ((α : ℤ) * t) * g ((β : ℤ) * t) := by
  have hW : 1 + integerDivisorMask ρ t ≠ 0 := by
    have h := integerDivisorMask_nonneg_of_mass_nonneg ρ hρ t
    linarith
  unfold divisorWeightedMerge
  rw [mul_comm]
  exact div_mul_cancel₀ _ hW

namespace MaskColumnPlan

variable {m : ℕ} {S U : Finset (Fin (m + 1))}

def absorbedScalar (P : MaskColumnPlan S U) (p q : ℕ) (t : Fin 3) : ℕ :=
  match P with
  | .outside _ _ _ => maskSingleScalar p t
  | .balanced _ _ _ _ _ _ _ => maskAbsorbedScalar p q t

theorem absorbedScalar_coprime (P : MaskColumnPlan S U) (p q d : ℕ)
    (hp : p.Coprime d) (hq : q.Coprime d) (t : Fin 3) :
    (P.absorbedScalar p q t).Coprime d := by
  cases P <;> unfold absorbedScalar maskSingleScalar maskAbsorbedScalar <;> split_ifs
  all_goals first | exact hp | exact hq | exact Nat.coprime_one_left d

theorem invariantIntegerForm_absorbed {n r : ℕ} (P : MaskColumnPlan S U)
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (i : Fin r)
    (hi : maskRowInvariant (F.row i) P.tag) (p q : ℕ) (z : Fin (m + 1) → ℤ) :
    F.normalizedIntegerLinearForm x c i (P.absorbedCoordinates p q z) =
      (P.absorbedScalar p q (P.tag (F.normalizationAnchor i)) : ℤ) *
        F.normalizedIntegerLinearForm x c i z := by
  cases P with
  | outside u hu hU => exact F.invariantIntegerForm_single x c i u hi p z
  | balanced u v hu hv huU hvU hne => exact F.invariantIntegerForm_absorbed x c i u v hne hi p q z

end MaskColumnPlan

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

noncomputable def maskStageRowDivisorMass (k w : ℕ)
    (i : Fin (maskPrefixRowStage S hS k).rowCount) : Mass ℕ :=
  tailMass (primorial w) ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w)
    ((maskPrefixRowStage S hS k).rows.normalizationAnchor i))

noncomputable def maskStageRowMajorant (k w : ℕ)
    (i : Fin (maskPrefixRowStage S hS k).rowCount) (t : ℤ) : ℝ :=
  1 + integerDivisorMask (maskStageRowDivisorMass S hS gap C k w i) t

noncomputable def maskStageInvariantMergedFunction (k : ℕ) (U : Finset (Fin (m + 1)))
    (w p q : ℕ) (i : Fin (maskPrefixRowStage S hS k).rowCount) (f g : ℤ → ℝ) : ℤ → ℝ :=
  divisorWeightedMerge (maskStageRowDivisorMass S hS gap C k w i)
    ((chosenMaskColumnPlan S U hS).absorbedScalar p q
      ((chosenMaskColumnPlan S U hS).tag ((maskPrefixRowStage S hS k).rows.normalizationAnchor i)))
    ((chosenMaskColumnPlan S U hS).absorbedScalar q p
      ((chosenMaskColumnPlan S U hS).tag ((maskPrefixRowStage S hS k).rows.normalizationAnchor i))) f g

include hC in
theorem maskStageRowDivisorMass_eventually_nonneg :
    ∀ᶠ w in atTop, ∀ k i d, 0 ≤ maskStageRowDivisorMass S hS gap C k w i d := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.raw_cutoffs_valid] with w hv
  intro k i d
  exact tailMass_nonneg (primorial_pos w) _ (chain_tailCutoffs_valid (C w)
    ((maskGeneratedMaster m gap).cutoff w) (primorial w) (hC w)
    (fun j hj => ⟨(hv j hj).1, (hv j hj).2.1⟩) _) d

include hC in
theorem maskStageRowMajorant_eventually_positive :
    ∀ᶠ w in atTop, ∀ k i t, 0 < maskStageRowMajorant S hS gap C k w i t := by
  filter_upwards [maskStageRowDivisorMass_eventually_nonneg S hS gap C hC] with w hw
  intro k i t
  have h := integerDivisorMask_nonneg_of_mass_nonneg _ (hw k i) t
  dsimp [maskStageRowMajorant]
  linarith

include hC htail in
theorem maskStageInvariantMergedFunction_eventually_bound :
    ∀ᶠ w in atTop, ∀ k U i,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ f g : ℤ → ℝ,
      (∀ t, |f t| ≤ maskStageRowMajorant S hS gap C k w i t) →
      (∀ t, |g t| ≤ maskStageRowMajorant S hS gap C k w i t) → ∀ t,
      |maskStageInvariantMergedFunction S hS gap C k U w p q i f g t| ≤
        maskStageRowMajorant S hS gap C k w i t := by
  filter_upwards [maskStageRowDivisorMass_eventually_nonneg S hS gap C hC,
    maskTail_fresh_prime_units gap C hC htail] with w hn hu
  intro k U i p hp q hq f g hf hg t
  apply divisorWeightedMerge_bound _ (hn k i) _ _ _ _ f g hf hg t
  · intro d hd
    exact (chosenMaskColumnPlan S U hS).absorbedScalar_coprime p q d
      (hu _ p hp d hd) (hu _ q hq d hd) _
  · intro d hd
    exact (chosenMaskColumnPlan S U hS).absorbedScalar_coprime q p d
      (hu _ q hq d hd) (hu _ p hp d hd) _

include hC in
theorem maskStageInvariantMergedFunction_eventually_factorization
    (a : Fin (m + 1) → ℚ) :
    ∀ᶠ w in atTop, ∀ k U i, i ∈ maskStageInvariantRows S hS k U →
      ∀ p q : ℕ, ∀ f g : ℤ → ℝ, ∀ x z,
      maskStageRowMajorant S hS gap C k w i
        ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
          (masterColumnCoefficient N a (fun w => (C w).block) w) i z) *
      maskStageInvariantMergedFunction S hS gap C k U w p q i f g
        ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
          (masterColumnCoefficient N a (fun w => (C w).block) w) i z) =
      f ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
          (masterColumnCoefficient N a (fun w => (C w).block) w) i
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates p q z)) *
      g ((maskPrefixRowStage S hS k).rows.normalizedIntegerLinearForm x
          (masterColumnCoefficient N a (fun w => (C w).block) w) i
          ((chosenMaskColumnPlan S U hS).absorbedCoordinates q p z)) := by
  filter_upwards [maskStageRowDivisorMass_eventually_nonneg S hS gap C hC] with w hn
  intro k U i hi p q f g x z
  rw [(chosenMaskColumnPlan S U hS).invariantIntegerForm_absorbed
    (maskPrefixRowStage S hS k).rows x _ i (Finset.mem_filter.mp hi).2 p q z,
    (chosenMaskColumnPlan S U hS).invariantIntegerForm_absorbed
    (maskPrefixRowStage S hS k).rows x _ i (Finset.mem_filter.mp hi).2 q p z]
  exact divisorWeightedMerge_factorization _ (hn k i) _ _ f g _

end Hindman168
