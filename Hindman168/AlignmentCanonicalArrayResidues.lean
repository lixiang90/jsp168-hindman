import Hindman168.AlignmentExposureArrayGoodEvent
import Hindman168.AlignmentExposedArrayOffsets

namespace Hindman168

theorem alignmentIntegerArrayArgument_residue {n : ℕ} {i : Fin n}
    (t : Fin n → ℕ) (M : ℕ) (ρ : AlignmentAddingPair n i → ℕ)
    (Δ : AlignmentAddingPair n i → ℤ) (T : Finset (Fin n))
    (p : ℤ) (v u : AlignmentAddingPair n i → ℤ) :
    alignmentIntegerArrayArgument t M ρ Δ T p v u % (M : ℤ) =
      alignmentPivotArrayResidue t T M p (alignmentIntegerSlotShift ρ v) := by
  unfold alignmentIntegerArrayArgument alignmentPivotArrayResidue
  simp only [Int.add_emod, Int.mul_emod, Int.emod_self, zero_mul, Int.zero_emod, add_zero,
    Int.emod_emod]

theorem alignment_shortExposure_canonical_residue
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (q₀ w : ℕ) (i : Fin n)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i) {x y : Fin n → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w)) (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (p : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (v u : AlignmentAddingPair n i → ℤ) :
    alignmentIntegerArrayArgument y (F.modulus w)
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
      (fun e => alignmentPairProgression q₀ w (F.modulus w) e y) T p v u % (F.modulus w : ℤ) =
    alignmentPivotArrayResidue x T (F.modulus w) (x i)
      (alignmentIntegerSlotShift (fun e => alignmentPairResidue q₀ w (F.modulus w) e x) v) := by
  rw [alignmentIntegerArrayArgument_residue]
  have hexp := alignmentShortExposureKey_rawExposure F w i T hkey
  have hs := alignmentRawExposure_slot_shift_eq hF q₀ w hx hy hexp v
  have ht := alignmentRawExposure_tail_modEq hexp hT (dvd_mul_right (F.modulus w : ℕ) _)
  have hxy : Int.ModEq (F.modulus w : ℕ) (x i) (y i) :=
    Int.natCast_modEq_iff.mpr (alignmentShortExposureKey_pivot_residue F w i T hkey)
  unfold alignmentPivotArrayResidue
  rw [← hs]
  exact ht.symm.mul ((hp.trans hxy.symm).add_right _)

theorem alignment_exposure_canonical_piece
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀ + 1 ≤ w)
    (i : Fin n) (C : ℕ) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) {x y : Fin n → ℕ}
    (hgood : alignmentExposureArrayStable F w i q₀ C T V U x)
    (hx : ∀ j, Nat.Coprime (x j) (primorial w)) (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hcut : ∀ j, j < i → y j ≤ F.cutoff w j.val ^ 2)
    (hkey : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (v : AlignmentAddingPair n i → ℤ) (hv : v ∈ V)
    (u : AlignmentAddingPair n i → ℤ) (hu : u ∈ U)
    (p : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (hdist : |p - y i| ≤ (C * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ)) :
    intervalResiduePiece (F.gap w i.val) (F.modulus w)
      (alignmentIntegerArrayArgument y (F.modulus w)
        (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
        (fun e => alignmentPairProgression q₀ w (F.modulus w) e y) T p v u) =
      (((alignmentNaturalBlockProduct x T * x i : ℕ) : ℤ) / (F.gap w i.val : ℤ),
        alignmentPivotArrayResidue x T (F.modulus w) (x i)
          (alignmentIntegerSlotShift (fun e => alignmentPairResidue q₀ w (F.modulus w) e x) v)) := by
  apply Prod.ext
  · exact hgood y hcut hkey v hv u hu _
      (fun e => (alignmentPairResidue_master_data hF hq hw y hy e).2.1.le) _
      (fun e => alignmentPairProgression_exact hF hq hw y hy e) p hdist
  · exact alignment_shortExposure_canonical_residue hF q₀ w i T hT hx hy hkey p hp v u

end Hindman168
