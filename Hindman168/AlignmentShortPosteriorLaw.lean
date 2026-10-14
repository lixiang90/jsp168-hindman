import Hindman168.AlignmentPreShortConditioning
import Hindman168.DyadicShortBinPosterior

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

theorem alignment_shortExposure_tailPivot_event
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (w : ℕ) (i : Fin n) (T : Finset (Fin n))
    (hT : ∀ j ∈ T, j < i) (x : Fin n → ℕ)
    (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support)
    (hZ : ∀ j : Fin n, 0 < harmonicNormalizer (F.cutoff w j.val) (primorial w))
    (hR : 0 < alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
    (B : (T → ℕ) × ℕ → Prop) :
    let V := (∏ j ∈ T, 2 ^ Nat.log2 (x j)) *
      alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)
    let Q := (alignmentNaturalBlockProduct x T * x i / V) * V
    event (conditionMass (globalRawMass (F.cutoff w) (primorial w) n)
      (fun y => alignmentShortExposureKey F w i T y = alignmentShortExposureKey F w i T x))
      (fun y => B (fun j : T => y j.val, y i)) =
    event (conditionMass (conditionalJoint
      (dyadicHarmonicTailMass (fun j : T => F.cutoff w j.val.val) (primorial w)
        (fun j => binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j.val)))
      (fun _ => rawMass (F.cutoff w i.val) (primorial w)))
      (fun yp => Q ≤ (∏ j, yp.1 j) * yp.2 ∧ (∏ j, yp.1 j) * yp.2 < Q + V ∧
        yp.2 % (F.modulus w : ℕ) = x i % (F.modulus w : ℕ))) B := by
  dsimp only
  rw [alignment_shortExposure_condition_exact hF w i T x hR]
  let V := (∏ j ∈ T, 2 ^ Nat.log2 (x j)) *
    alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)
  let Q := (alignmentNaturalBlockProduct x T * x i / V) * V
  let P : (T → ℕ) × ℕ → Prop := fun yp =>
    Q ≤ (∏ j, yp.1 j) * yp.2 ∧ (∏ j, yp.1 j) * yp.2 < Q + V ∧
      yp.2 % (F.modulus w : ℕ) = x i % (F.modulus w : ℕ)
  have h := conditioned_piMass_tailPivot_event
    (fun j : Fin n => rawMass (F.cutoff w j.val) (primorial w))
    (alignmentPreShortEvent F w i T x) (alignmentPreShortEvent_pos hF w i T x hx hZ)
    (alignmentTailPivotIndex i T) (alignmentTailPivotIndex_injective i T hT) P B
  have hc : (fun y : Fin n → ℕ => (∀ j, alignmentPreShortEvent F w i T x j (y j)) ∧
      P (fun k => y (alignmentTailPivotIndex i T (some k)), y (alignmentTailPivotIndex i T none))) =
    (fun y => (∀ j, j < i → j ∉ T → x j = y j) ∧
      (∀ j ∈ T, y j ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j)) ∧
      y i % (F.modulus w : ℕ) = x i % (F.modulus w : ℕ) ∧
      Q ≤ alignmentNaturalBlockProduct y T * y i ∧
      alignmentNaturalBlockProduct y T * y i < Q + V) := by
    funext y
    apply propext
    rw [alignmentPreShortEvent_all]
    dsimp only [P, alignmentTailPivotIndex]
    rw [Finset.prod_coe_sort]
    unfold alignmentNaturalBlockProduct
    tauto
  rw [hc] at h
  simp only [alignmentTailPivotIndex, alignmentPreShortEvent_tail,
    alignmentPreShortEvent_pivot F w i T x hT,
    conditionMass_true_of_total_one _ (rawMass_total (hZ i))] at h
  exact h

end Hindman168
