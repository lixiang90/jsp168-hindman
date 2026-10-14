import Hindman168.MaskInitialSubsetForms
import Hindman168.FiniteEmptyCoordinateLaw

/-! Construct the actual initial input from the paper's subset functions.
The initial prime tuple is empty, so its exact law disappears with unit
mass, retaining the original independent harmonic coordinate laws. -/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (C : ℕ → Chain (m+1))

noncomputable def maskSubsetTailMask (w : ℕ) (U : NonemptyColumnSubset (m+1)) (y : ℤ) : ℝ :=
  integerDivisorMask (tailMass (primorial w)
    ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (U.val.max' U.property))) y

theorem maskInitialSubset_majorant (w : ℕ) (U : NonemptyColumnSubset (m+1)) :
    maskFamilyRowMajorant gap C (initialMaskRowFamily (R := MvPolynomial (Fin 0) ℤ) m) w
      (initialMaskRowIndex U.val U.property) = fun y => 1 + maskSubsetTailMask gap C w U y := by
  funext y
  unfold maskFamilyRowMajorant maskFamilyRowDivisorMass maskSubsetTailMask
  rw [initialMaskRowFamily_normalizationAnchor]

variable (S : Finset (Fin (m+1))) (hS : 2 ≤ S.card)

noncomputable def maskInitialSubsetInput (w : ℕ)
    (f : NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ)
    (hf : ∀ U y, |f U y| ≤ 1 + maskSubsetTailMask gap C w U y)
    (hb : ∀ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅, ∀ y, |b V y| ≤ 1) :
    MaskStageCorrelationInput S hS gap C 0 w (maskRemainingMasks m 0) where
  rows := fun _ i => f ((Fintype.equivFin (NonemptyColumnSubset (m+1))).symm i)
  masks := fun _ => b
  row_bound := by
    intro x hx i y
    let U : NonemptyColumnSubset (m+1) := (Fintype.equivFin _).symm i
    have hi : initialMaskRowIndex U.val U.property = i := by
      simp [U, initialMaskRowIndex]
    change |f U y| ≤ maskFamilyRowMajorant gap C
      (initialMaskRowFamily (R := MvPolynomial (Fin 0) ℤ) m) w i y
    rw [← hi, maskInitialSubset_majorant]
    exact hf U y
  mask_bound := by
    intro x hx V hV y
    rw [maskRemainingMasks_zero] at hV
    exact hb V hV y

theorem maskInitialCenteredTarget_subset (w : ℕ) :
    maskInitialCenteredTarget gap C S hS w =
      fun y => maskSubsetTailMask gap C w ⟨S, Finset.card_pos.mp (by omega)⟩ y - 1 := by
  funext y
  change integerDivisorMask (tailMass (primorial w)
    ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w)
      ((initialMaskRowFamily (R := MvPolynomial (Fin 0) ℤ) m).normalizationAnchor
        (initialMaskRowIndex S (Finset.card_pos.mp (by omega)))))) y - 1 = _
  rw [initialMaskRowFamily_normalizationAnchor ⟨S, Finset.card_pos.mp (by omega)⟩]
  rfl

theorem maskInitialSubsetInput_target (w : ℕ)
    (f : NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ)
    (hf : ∀ U y, |f U y| ≤ 1 + maskSubsetTailMask gap C w U y)
    (hb : ∀ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅, ∀ y, |b V y| ≤ 1)
    (ht : f ⟨S, Finset.card_pos.mp (by omega)⟩ =
      fun y => maskSubsetTailMask gap C w ⟨S, Finset.card_pos.mp (by omega)⟩ y - 1) :
    maskStageInputHasTarget S hS gap C (maskInitialSubsetInput gap C S hS w f b hf hb)
      (maskInitialCenteredTarget gap C S hS w) := by
  intro x
  change f ((Fintype.equivFin (NonemptyColumnSubset (m+1))).symm
    (initialMaskRowIndex S (Finset.card_pos.mp (by omega)))) = _
  simp only [initialMaskRowIndex, Equiv.symm_apply_apply]
  rw [ht, maskInitialCenteredTarget_subset]

noncomputable def maskOriginalSubsetCorrelation (w : ℕ)
    (f : NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ) : ℝ :=
  expectation (maskOriginalBaseMass m gap C w) (fun z =>
    (∏ U : NonemptyColumnSubset (m+1),
      f U (maskSubsetIntegerForm (masterColumnCoefficient N a (fun w => (C w).block) w) U z)) *
    ∏ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅, b V (∏ k ∈ V, z k))

theorem maskInitialSubsetInput_correlation (w : ℕ)
    (f : NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ)
    (hf : ∀ U y, |f U y| ≤ 1 + maskSubsetTailMask gap C w U y)
    (hb : ∀ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅, ∀ y, |b V y| ≤ 1) :
    maskStageInputCorrelation S hS gap a C (maskInitialSubsetInput gap C S hS w f b hf hb) =
      maskOriginalSubsetCorrelation gap a C w f b := by
  change maskRowMaskCorrelation gap C (initialMaskRowFamily (R := MvPolynomial (Fin 0) ℤ) m)
    (masterColumnCoefficient N a (fun w => (C w).block) w) w (maskRemainingMasks m 0)
    (fun _ => b) (fun _ i => f ((Fintype.equivFin (NonemptyColumnSubset (m+1))).symm i)) = _
  unfold maskRowMaskCorrelation monomialRowPrimeMass masterPrimeSlotsMass
  rw [piMass_empty_expectation]
  simp_rw [initialMaskRowFamily_integerProduct, maskRemainingMasks_zero]
  rfl

end Hindman168
