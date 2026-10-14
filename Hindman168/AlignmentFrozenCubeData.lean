import Hindman168.AlignmentMasterRetainedCRT
import Hindman168.AlignmentCanonicalArrayResidues
import Hindman168.AlignmentShortPosteriorBound

namespace Hindman168
open scoped BigOperators

theorem alignmentShortExposureKey_volume_eq {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) {x y : Fin n → ℕ}
    (h : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y) :
    alignmentShortBinVolume F w i T x = alignmentShortBinVolume F w i T y := by
  unfold alignmentShortBinVolume
  rw [alignmentShortExposureKey_lower_product F w i T h]

theorem alignmentShortExposureKey_start_eq {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) {x y : Fin n → ℕ}
    (h : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y) :
    alignmentShortBinStart F w i T x = alignmentShortBinStart F w i T y := by
  have hv := alignmentShortExposureKey_volume_eq F w i T h
  have hb := alignmentShortExposureKey_product_bin F w i T h
  change _ / alignmentShortBinVolume F w i T x = _ / alignmentShortBinVolume F w i T x at hb
  unfold alignmentShortBinStart
  rw [← hv, hb]

theorem alignmentShortExposureKey_arrayResidue_eq {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    {x y : Fin n → ℕ}
    (h : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (p s : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i)) :
    alignmentPivotArrayResidue y T (F.modulus w) p s =
      alignmentPivotArrayResidue x T (F.modulus w) (x i) s := by
  have ht := alignmentRawExposure_tail_modEq
    (alignmentShortExposureKey_rawExposure F w i T h) hT
    (dvd_mul_right (F.modulus w : ℕ) ((primorial w) ^ w))
  have hi := Int.natCast_modEq_iff.mpr (alignmentShortExposureKey_pivot_residue F w i T h)
  exact ht.symm.mul ((hp.trans hi.symm).add_right s)

theorem alignmentShortExposureKey_retained_representative {n : ℕ} (F : MasterParameterFamily)
    (w d : ℕ) (i : Fin n) (T U : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    {x y : Fin n → ℕ}
    (h : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (hU : ∀ j ∈ U, x j = y j) (c : ℤ) :
    alignmentRetainedRepresentative (F.modulus w) d (alignmentNaturalBlockProduct y U)
      ((alignmentShortBinStart F w i T y : ℤ) / (F.modulus w : ℤ))
      (alignmentPivotArrayResidue y T (F.modulus w) (y i) 0) c =
    alignmentRetainedRepresentative (F.modulus w) d (alignmentNaturalBlockProduct x U)
      ((alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ))
      (alignmentPivotArrayResidue x T (F.modulus w) (x i) 0) c := by
  rw [← alignmentNaturalBlockProduct_congr x y U hU,
    ← alignmentShortExposureKey_start_eq F w i T h,
    alignmentShortExposureKey_arrayResidue_eq F w i T hT h (y i) 0 (Int.ModEq.refl _)]

end Hindman168
