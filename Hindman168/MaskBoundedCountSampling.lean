import Hindman168.OriginalChainWeightedSampling
import Hindman168.SubsetSingletonFactors
import Hindman168.MaskSubsetReplacementPath

/-! The paper's bounded model count retains the complete product mask.
Singleton sum rows are the original center weights. Only nonsingleton
sum rows are models. All sampling comparison masses are left intact. -/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

noncomputable def maskCenterAndRows {m N : ℕ} (gap : ℕ → Fin N)
    (C : ℕ → Chain (m+1)) (w : ℕ) (ρ : Fin (m+1) → ℤ → ℝ)
    (U : NonemptyColumnSubset (m+1)) : ℤ → ℝ :=
  if 2 ≤ U.val.card then ρ (U.val.max' U.property) else maskSubsetTailMask gap C w U

noncomputable def maskBoundedCountIntegrand {m N : ℕ} (_gap : ℕ → Fin N)
    (a : Fin (m+1) → ℚ) (C : ℕ → Chain (m+1)) (w : ℕ)
    (S : Fin (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ)
    (z : Fin (m+1) → ℤ) : ℝ :=
  (∏ U : NonemptyColumnSubset (m+1), if 2 ≤ U.val.card then
    S (U.val.max' U.property)
      (maskSubsetIntegerForm (masterColumnCoefficient N a (fun w => (C w).block) w) U z)
    else 1) *
    ∏ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅, b V (∏ k ∈ V, z k)

theorem maskCenterAndRows_replacement {m N : ℕ} (gap : ℕ → Fin N)
    (C : ℕ → Chain (m+1)) (w : ℕ) (ρ S : Fin (m+1) → ℤ → ℝ) :
    maskSubsetModelReplacement (maskCenterAndRows gap C w ρ) S =
      maskCenterAndRows gap C w S := by
  funext U y
  by_cases hU : 2 ≤ U.val.card <;>
    simp [maskSubsetModelReplacement, maskCenterAndRows, hU]

theorem maskCenterAndRows_bounded_count {m N : ℕ} (gap : ℕ → Fin N)
    (a : Fin (m+1) → ℚ) (C : ℕ → Chain (m+1)) (w : ℕ)
    (hc : ∀ col, 0 < masterColumnCoefficient N a (fun w => (C w).block) w col)
    (S : Fin (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ) :
    maskOriginalSubsetCorrelation gap a C w (maskCenterAndRows gap C w S) b =
      expectation (maskOriginalBaseMass m gap C w) (fun z =>
        (∏ col, integerDivisorMask (tailMass (primorial w)
          ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) col)) (z col)) *
        maskBoundedCountIntegrand gap a C w S b z) := by
  unfold maskOriginalSubsetCorrelation
  apply congrArg (expectation (maskOriginalBaseMass m gap C w))
  funext z
  have he (U : NonemptyColumnSubset (m+1)) :
      maskCenterAndRows gap C w S U
        (maskSubsetIntegerForm (masterColumnCoefficient N a (fun w => (C w).block) w) U z) =
      (if 2 ≤ U.val.card then 1 else maskSubsetTailMask gap C w U
        (maskSubsetIntegerForm (masterColumnCoefficient N a (fun w => (C w).block) w) U z)) *
      (if 2 ≤ U.val.card then S (U.val.max' U.property)
        (maskSubsetIntegerForm (masterColumnCoefficient N a (fun w => (C w).block) w) U z) else 1) := by
    unfold maskCenterAndRows
    split_ifs <;> simp
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  have hs := subset_center_product (masterColumnCoefficient N a (fun w => (C w).block) w)
    hc (fun col => integerDivisorMask (tailMass (primorial w)
      ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) col))) z
  change (∏ U : NonemptyColumnSubset (m+1), if 2 ≤ U.val.card then 1 else
    maskSubsetTailMask gap C w U
      (maskSubsetIntegerForm (masterColumnCoefficient N a (fun w => (C w).block) w) U z)) = _ at hs
  rw [hs]
  exact mul_assoc _ _ _

theorem maskBoundedCountIntegrand_unit {m N : ℕ} (gap : ℕ → Fin N)
    (a : Fin (m+1) → ℚ) (C : ℕ → Chain (m+1)) (w : ℕ)
    (S : Fin (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ)
    (hS : ∀ col y, 0 ≤ S col y ∧ S col y ≤ 1)
    (hb : ∀ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅, ∀ y, |b V y| ≤ 1)
    (z : Fin (m+1) → ℤ) : |maskBoundedCountIntegrand gap a C w S b z| ≤ 1 := by
  unfold maskBoundedCountIntegrand
  rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
  have hr : (∏ U : NonemptyColumnSubset (m+1),
      |if 2 ≤ U.val.card then S (U.val.max' U.property)
        (maskSubsetIntegerForm (masterColumnCoefficient N a (fun w => (C w).block) w) U z) else 1|) ≤ 1 := by
    apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
    intro U _
    split_ifs
    · rw [abs_of_nonneg (hS _ _).1]
      exact (hS _ _).2
    · norm_num
  have hm : (∏ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅,
      |b V (∏ k ∈ V, z k)|) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun V hV => hb V hV _)
  exact (mul_le_mul hr hm (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
    (by norm_num)).trans_eq (by norm_num)

theorem mask_bounded_count_sampling_uniform {m N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (ha : ∀ col, 0 < a col)
    (C : ℕ → Chain (m+1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ w in atTop, ∀ (S : Fin (m+1) → ℤ → ℝ)
      (b : Finset (Fin (m+1)) → ℤ → ℝ),
      (∀ col y, 0 ≤ S col y ∧ S col y ≤ 1) →
      (∀ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅, ∀ y, |b V y| ≤ 1) →
      |maskOriginalSubsetCorrelation gap a C w (maskCenterAndRows gap C w S) b -
        expectation (globalRawMass ((maskGeneratedMaster m gap).cutoff w) (primorial w) N)
          (fun x => maskBoundedCountIntegrand gap a C w S b
            (fun col => ((C w).sampleProducts (hC w) x col : ℤ)))| < η := by
  let A := Finset.univ.image a
  have hA : ∀ v ∈ A, 0 < v := by
    intro v hv
    obtain ⟨col, _, rfl⟩ := Finset.mem_image.mp hv
    exact ha col
  have hF := maskGeneratedMaster_conditions m gap A hA
  have hc := hF.column_coefficients a (fun col => Finset.mem_image.mpr ⟨col, by simp, rfl⟩)
    (fun w => (C w).block) hC (fun w col => (C w).block_nonempty col)
  have ht := hF.chain_weighted_testing_uniform C hC η hη
  filter_upwards [hc, ht] with w hcw htw
  intro S b hS hb
  rw [maskCenterAndRows_bounded_count gap a C w (fun col => (hcw col).1) S b, abs_sub_comm]
  exact htw _ (maskBoundedCountIntegrand_unit gap a C w S b hS hb)

theorem maskCenterAndRows_admissible {m N : ℕ} (gap : ℕ → Fin N)
    (C : ℕ → Chain (m+1)) (w : ℕ) (ρ : Fin (m+1) → ℤ → ℝ)
    (b : Finset (Fin (m+1)) → ℤ → ℝ)
    (hν : ∀ U : NonemptyColumnSubset (m+1), ∀ y, 0 ≤ maskSubsetTailMask gap C w U y)
    (hρ : ∀ col y, 0 ≤ ρ col y ∧ ρ col y ≤
      integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) col)) y)
    (hb : ∀ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅, ∀ y, |b V y| ≤ 1) :
    maskOriginalSubsetAdmissible gap C w (maskCenterAndRows gap C w ρ) b := by
  refine ⟨?_, hb⟩
  intro U y
  unfold maskCenterAndRows
  split_ifs
  · rw [abs_of_nonneg (hρ _ y).1]
    exact (hρ _ y).2.trans (by
      change maskSubsetTailMask gap C w U y ≤ 1 + maskSubsetTailMask gap C w U y
      linarith)
  · rw [abs_of_nonneg (hν U y)]
    linarith

theorem mask_original_count_sampling_transfer {m N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (ha : ∀ col, 0 < a col)
    (C : ℕ → Chain (m+1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (ρ S : Fin (m+1) → ℕ → ℤ → ℝ)
    (hS : ∀ col w y, 0 ≤ S col w y ∧ S col w y ≤ 1)
    (b : ℕ → Finset (Fin (m+1)) → ℤ → ℝ)
    (hb : ∀ᶠ w in (U : Filter ℕ),
      ∀ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅, ∀ y, |b w V y| ≤ 1)
    (δ : ℝ)
    (hreplace : ∀ᶠ w in (U : Filter ℕ),
      |maskOriginalSubsetCorrelation gap a C w
          (maskCenterAndRows gap C w (fun col => ρ col w)) (b w) -
        maskOriginalSubsetCorrelation gap a C w
          (maskCenterAndRows gap C w (fun col => S col w)) (b w)| ≤ δ)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ w in (U : Filter ℕ),
      |maskOriginalSubsetCorrelation gap a C w
          (maskCenterAndRows gap C w (fun col => ρ col w)) (b w) -
        expectation (globalRawMass ((maskGeneratedMaster m gap).cutoff w) (primorial w) N)
          (fun x => maskBoundedCountIntegrand gap a C w (fun col => S col w) (b w)
            (fun col => ((C w).sampleProducts (hC w) x col : ℤ)))| < δ + η := by
  have hs := hU (mask_bounded_count_sampling_uniform gap a ha C hC η hη)
  filter_upwards [hreplace, hb, hs] with w hw hbw hsw
  have ht := hsw (fun col => S col w) (b w) (fun col => hS col w) hbw
  calc
    _ ≤ |maskOriginalSubsetCorrelation gap a C w
          (maskCenterAndRows gap C w (fun col => ρ col w)) (b w) -
        maskOriginalSubsetCorrelation gap a C w
          (maskCenterAndRows gap C w (fun col => S col w)) (b w)| +
        |maskOriginalSubsetCorrelation gap a C w
          (maskCenterAndRows gap C w (fun col => S col w)) (b w) -
        expectation (globalRawMass ((maskGeneratedMaster m gap).cutoff w) (primorial w) N)
          (fun x => maskBoundedCountIntegrand gap a C w (fun col => S col w) (b w)
            (fun col => ((C w).sampleProducts (hC w) x col : ℤ)))| := abs_sub_le _ _ _
    _ < δ + η := add_lt_add_of_le_of_lt hw ht

end Hindman168
