import Hindman168.AlignmentShortPosteriorLaw
import Hindman168.NaturalDyadicShortPosterior

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

noncomputable def alignmentShortBinVolume {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ) : ℕ :=
  (∏ j ∈ T, 2 ^ Nat.log2 (x j)) * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)

noncomputable def alignmentShortBinStart {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ) : ℕ :=
  (alignmentNaturalBlockProduct x T * x i / alignmentShortBinVolume F w i T x) *
    alignmentShortBinVolume F w i T x

theorem alignment_shortExposure_tail_posterior
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (w : ℕ) (i : Fin n) (T : Finset (Fin n))
    (hT : ∀ j ∈ T, j < i) (x : Fin n → ℕ)
    (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support)
    (hZ : ∀ j : Fin n, 0 < harmonicNormalizer (F.cutoff w j.val) (primorial w))
    (hWM : primorial w ∣ (F.modulus w : ℕ))
    (hgood : ∀ j ∈ T, binaryDyadicCutoffGood (F.cutoff w j.val) (x j))
    (hR : 0 < alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
    (hQ : 0 < alignmentShortBinStart F w i T x)
    (hwidth : alignmentShortBinVolume F w i T x ≤ alignmentShortBinStart F w i T x)
    (hcutlo : F.cutoff w i.val * (2 ^ T.card * ∏ j ∈ T, 2 ^ Nat.log2 (x j)) ≤
      alignmentShortBinStart F w i T x)
    (hcuthi : alignmentShortBinStart F w i T x + alignmentShortBinVolume F w i T x ≤
      F.cutoff w i.val ^ 2 * ∏ j ∈ T, 2 ^ Nat.log2 (x j))
    (hsmall : 2 * (2 ^ T.card : ℝ) * (F.modulus w : ℕ) /
      alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) ≤ 1 / 2)
    (B : (T → ℕ) → Prop) :
    event (conditionMass (globalRawMass (F.cutoff w) (primorial w) n)
      (fun y => alignmentShortExposureKey F w i T y = alignmentShortExposureKey F w i T x))
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
    hQ hR (by simpa only [hprod, alignmentShortBinVolume] using hwidth)
    (by simpa only [Fintype.card_coe, hprod] using hcutlo)
    (by simpa only [hprod, alignmentShortBinVolume] using hcuthi)
    (F.modulus w).pos (Nat.mod_lt _ (F.modulus w).pos) hWM
    ((residue_coprime_iff (primorial w) (F.modulus w) (x i % (F.modulus w : ℕ))
      (x i) hWM rfl).mp (alignmentGlobalRawMass_support_coprime F w x hx i))
    (hZ i) (by simpa only [Fintype.card_coe] using hsmall) B
  have he := alignment_shortExposure_tailPivot_event hF w i T hT x hx hZ hR (fun yp => B yp.1)
  dsimp only at he
  rw [he]
  simpa only [Fintype.card_coe, hprod, alignmentShortBinStart, alignmentShortBinVolume] using hp

end Hindman168
