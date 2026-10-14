import Hindman168.AlignmentTypicalShortPosterior
import Hindman168.SelectedAlignmentGeometryView

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

theorem selected_alignment_shortExposure_condition_exact
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (gap : ℕ) (w : ℕ) (i : Fin n) (T : Finset (Fin n))
    (x : Fin n → ℕ)
    (hR : 0 < alignedSqrtMicrocellWidth (F.gap w gap) (F.modulus w)) :
    let V := (∏ j ∈ T, 2 ^ Nat.log2 (x j)) *
      alignedSqrtMicrocellWidth (F.gap w gap) (F.modulus w)
    let Q := (alignmentNaturalBlockProduct x T * x i / V) * V
    conditionMass (globalRawMass (F.cutoff w) (primorial w) n)
      (fun y => alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y = alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x) =
    conditionMass (globalRawMass (F.cutoff w) (primorial w) n)
      (fun y => (∀ j, j < i → j ∉ T → x j = y j) ∧
        (∀ j ∈ T, y j ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j)) ∧
        y i % (F.modulus w : ℕ) = x i % (F.modulus w : ℕ) ∧
        Q ≤ alignmentNaturalBlockProduct y T * y i ∧
        alignmentNaturalBlockProduct y T * y i < Q + V) := by
  dsimp only
  have hV : 0 < (∏ j ∈ T, 2 ^ Nat.log2 (x j)) *
      alignedSqrtMicrocellWidth (F.gap w gap) (F.modulus w) := by positivity
  apply conditionMass_congr_on_support
  intro y hy
  have hf := alignmentShortExposureKey_window_iff (alignmentGeometryWithGap F i.val gap) w i T x y
    (fun j _ => alignmentGlobalRawMass_support_positive hF w y hy j)
  simp only [alignmentGeometryWithGap_modulus, alignmentGeometryWithGap_gap] at hf
  rw [eq_comm] at hf
  rw [hf]
  constructor
  · rintro ⟨hout, hwin, hp, hb⟩
    exact ⟨hout, hwin, hp.symm, (sameNaturalShortBin_iff hV _ _).mp hb⟩
  · rintro ⟨hout, hwin, hp, hb⟩
    exact ⟨hout, hwin, hp.symm, (sameNaturalShortBin_iff hV _ _).mpr hb⟩


theorem selected_alignment_shortExposure_tailPivot_event
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (gap : ℕ) (w : ℕ) (i : Fin n) (T : Finset (Fin n))
    (hT : ∀ j ∈ T, j < i) (x : Fin n → ℕ)
    (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support)
    (hZ : ∀ j : Fin n, 0 < harmonicNormalizer (F.cutoff w j.val) (primorial w))
    (hR : 0 < alignedSqrtMicrocellWidth (F.gap w gap) (F.modulus w))
    (B : (T → ℕ) × ℕ → Prop) :
    let V := (∏ j ∈ T, 2 ^ Nat.log2 (x j)) *
      alignedSqrtMicrocellWidth (F.gap w gap) (F.modulus w)
    let Q := (alignmentNaturalBlockProduct x T * x i / V) * V
    event (conditionMass (globalRawMass (F.cutoff w) (primorial w) n)
      (fun y => alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y = alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x))
      (fun y => B (fun j : T => y j.val, y i)) =
    event (conditionMass (conditionalJoint
      (dyadicHarmonicTailMass (fun j : T => F.cutoff w j.val.val) (primorial w)
        (fun j => binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j.val)))
      (fun _ => rawMass (F.cutoff w i.val) (primorial w)))
      (fun yp => Q ≤ (∏ j, yp.1 j) * yp.2 ∧ (∏ j, yp.1 j) * yp.2 < Q + V ∧
        yp.2 % (F.modulus w : ℕ) = x i % (F.modulus w : ℕ))) B := by
  dsimp only
  rw [selected_alignment_shortExposure_condition_exact hF gap w i T x hR]
  let V := (∏ j ∈ T, 2 ^ Nat.log2 (x j)) *
    alignedSqrtMicrocellWidth (F.gap w gap) (F.modulus w)
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


theorem selected_alignment_shortExposure_tail_posterior
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (gap : ℕ) (w : ℕ) (i : Fin n) (T : Finset (Fin n))
    (hT : ∀ j ∈ T, j < i) (x : Fin n → ℕ)
    (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support)
    (hZ : ∀ j : Fin n, 0 < harmonicNormalizer (F.cutoff w j.val) (primorial w))
    (hWM : primorial w ∣ (F.modulus w : ℕ))
    (hgood : ∀ j ∈ T, binaryDyadicCutoffGood (F.cutoff w j.val) (x j))
    (hR : 0 < alignedSqrtMicrocellWidth (F.gap w gap) (F.modulus w))
    (hQ : 0 < alignmentShortBinStart (alignmentGeometryWithGap F i.val gap) w i T x)
    (hwidth : alignmentShortBinVolume (alignmentGeometryWithGap F i.val gap) w i T x ≤ alignmentShortBinStart (alignmentGeometryWithGap F i.val gap) w i T x)
    (hcutlo : F.cutoff w i.val * (2 ^ T.card * ∏ j ∈ T, 2 ^ Nat.log2 (x j)) ≤
      alignmentShortBinStart (alignmentGeometryWithGap F i.val gap) w i T x)
    (hcuthi : alignmentShortBinStart (alignmentGeometryWithGap F i.val gap) w i T x + alignmentShortBinVolume (alignmentGeometryWithGap F i.val gap) w i T x ≤
      F.cutoff w i.val ^ 2 * ∏ j ∈ T, 2 ^ Nat.log2 (x j))
    (hsmall : 2 * (2 ^ T.card : ℝ) * (F.modulus w : ℕ) /
      alignedSqrtMicrocellWidth (F.gap w gap) (F.modulus w) ≤ 1 / 2)
    (B : (T → ℕ) → Prop) :
    event (conditionMass (globalRawMass (F.cutoff w) (primorial w) n)
      (fun y => alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y = alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x))
      (fun y => B (fun j : T => y j.val)) ≤
    (3 * 2 ^ T.card) * event (piMass (fun j : T => uniformFinsetMass
      (binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j.val)))) B := by
  have hprod : (∏ j : T, (2 : ℕ) ^ Nat.log2 (x j.val)) = ∏ j ∈ T, 2 ^ Nat.log2 (x j) :=
    Finset.prod_coe_sort T (fun j => (2 : ℕ) ^ Nat.log2 (x j))
  have hp := dyadic_natural_shortBin_uniform_posterior
    (fun j : T => F.cutoff w j.val.val) (primorial w)
    (fun j : T => binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j.val))
    (fun j : T => 2 ^ Nat.log2 (x j.val))
    (fun _ => by positivity) (fun j => hZ j.val)
    (fun j => ⟨x j.val, binaryDyadicResidueWindow_anchor
      (alignmentGlobalRawMass_support_positive hF w x hx j.val)⟩)
    (fun j => binaryDyadicResidueWindow_subset (hgood j.val j.property)
      (hWM.trans (dvd_mul_right _ _)) (alignmentGlobalRawMass_support_coprime F w x hx j.val))
    (fun j p hp => by
      have hh := mem_residueWindow.mp hp
      exact ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2.1.le⟩)
    hQ hR (by simpa only [hprod, alignmentShortBinVolume, alignmentGeometryWithGap_gap, alignmentGeometryWithGap_modulus] using hwidth)
    (by simpa only [Fintype.card_coe, hprod] using hcutlo)
    (by simpa only [hprod, alignmentShortBinVolume, alignmentGeometryWithGap_gap, alignmentGeometryWithGap_modulus] using hcuthi)
    (F.modulus w).pos (Nat.mod_lt _ (F.modulus w).pos) hWM
    ((residue_coprime_iff (primorial w) (F.modulus w) (x i % (F.modulus w : ℕ))
      (x i) hWM rfl).mp (alignmentGlobalRawMass_support_coprime F w x hx i))
    (hZ i) (by simpa only [Fintype.card_coe] using hsmall) B
  have he := selected_alignment_shortExposure_tailPivot_event hF gap w i T hT x hx hZ hR (fun yp => B yp.1)
  dsimp only at he
  rw [he]
  simpa only [Fintype.card_coe, hprod, alignmentShortBinStart, alignmentShortBinVolume, alignmentGeometryWithGap_gap, alignmentGeometryWithGap_modulus] using hp


end Hindman168
