import Hindman168.MaskBlockGapTemplates
import Hindman168.MasterChainSampling
import Hindman168.FiniteWeightedErrors

/-! Exact original block-product sampling and its bounded comparison
with the original pivot law and divisor weight. -/

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical

noncomputable def originalBlockProductMass (F : MasterParameterFamily)
    (T : Finset ℕ) (i : ℕ) (hT : T.Nonempty) (hTi : T ⊆ Finset.range i) (w : ℕ) : Mass ℤ :=
  integerProductMass (tailMass (primorial w) ((maskBlockChain T i hT hTi).tailCutoffs (F.cutoff w) 0))
    (F.cutoff w i) (primorial w)

theorem originalBlockComparison_expectation (F : MasterParameterFamily)
    (T : Finset ℕ) (i : ℕ) (hT : T.Nonempty) (hTi : T ⊆ Finset.range i)
    (w : ℕ) (f : ℤ → ℝ) :
    expectation (integerProductComparisonMass
      (tailMass (primorial w) ((maskBlockChain T i hT hTi).tailCutoffs (F.cutoff w) 0))
      (F.cutoff w i) (primorial w)) f =
    expectation (integerMass (F.cutoff w i) (primorial w)) (fun y =>
      masterPredictionBlockMask F (fun _ => maskBlockChain T i hT hTi) (fun _ => 0) w y * f y) := by
  let ν := integerProductComparisonMass
    (tailMass (primorial w) ((maskBlockChain T i hT hTi).tailCutoffs (F.cutoff w) 0))
    (F.cutoff w i) (primorial w)
  have hs : ν.support ⊆ (integerMass (F.cutoff w i) (primorial w)).support := by
    intro y hy
    apply Finsupp.mem_support_iff.mpr
    intro hz
    apply Finsupp.mem_support_iff.mp hy
    change integerProductComparisonMass _ _ _ y = 0
    rw [integerProductComparisonMass_apply, hz, zero_mul]
  rw [expectation_eq_sum _ _ hs]
  simp only [ν, expectation, Finsupp.sum, integerProductComparisonMass_apply,
    masterPredictionBlockMask, mul_assoc]

theorem MasterParameterConditions.block_product_distance_tendsto {n N : ℕ}
    {A : Finset ℚ} {P : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A P F) (T : Finset ℕ) (i : Fin N)
    (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val) :
    Tendsto (fun w => distance (originalBlockProductMass F T i.val hT hTi w)
      (integerProductComparisonMass
        (tailMass (primorial w) ((maskBlockChain T i.val hT hTi).tailCutoffs (F.cutoff w) 0))
        (F.cutoff w i.val) (primorial w))) atTop (𝓝 0) := by
  have hg := hF.chain_sampling_growth (fun _ => maskBlockChain T i.val hT hTi)
    (fun _ => maskBlockChain_block_range T i hT hTi) (V := fun _ => 1)
    (Eventually.of_forall (fun w _ => by
      change 1 ≤ F.auxiliary w i.val
      have h := F.auxiliary_ge_two w i.val
      omega)) 0
  have hv : ∀ᶠ w in atTop, ValidCutoffs
      ((maskBlockChain T i.val hT hTi).tailCutoffs (F.cutoff w) 0) (primorial w) := by
    filter_upwards [hF.raw_cutoffs_valid] with w hw
    exact chain_tailCutoffs_valid (maskBlockChain T i.val hT hTi) (F.cutoff w) (primorial w)
      (maskBlockChain_block_range T i hT hTi) (fun j hj => ⟨(hw j hj).1, (hw j hj).2.1⟩) 0
  have hr := integer_block_product_law_rapid hg
    (Eventually.of_forall (fun _ => le_rfl)) (Eventually.of_forall primorial_pos) hv
  apply (Asymptotics.isLittleO_one_iff ℝ).mp
  simpa only [pow_zero, inv_one, Chain.cutoffs, maskBlockChain, originalBlockProductMass] using hr 0

theorem MasterParameterConditions.block_product_testing_uniform {n N : ℕ}
    {A : Finset ℚ} {P : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A P F) (T : Finset ℕ) (i : Fin N)
    (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ w in atTop, ∀ f : ℤ → ℝ, (∀ y, |f y| ≤ 1) →
      |expectation (originalBlockProductMass F T i.val hT hTi w) f -
        expectation (integerMass (F.cutoff w i.val) (primorial w)) (fun y =>
          masterPredictionBlockMask F (fun _ => maskBlockChain T i.val hT hTi)
            (fun _ => 0) w y * f y)| < η := by
  have ht := (hF.block_product_distance_tendsto T i hT hTi).eventually (Iio_mem_nhds hη)
  filter_upwards [ht] with w hw
  intro f hf
  rw [← originalBlockComparison_expectation F T i.val hT hTi w f]
  exact (expectation_difference_bound _ _ f 1 hf).trans_lt (by simpa only [one_mul] using hw)

end Hindman168
