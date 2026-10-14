import Hindman168.AlignmentIntegerArrayArguments
import Hindman168.NilPieceCubeGeometry

/-! The actual numerical array arguments stay in the pivot product's
H-interval when the corresponding explicit interior margin holds. -/

namespace Hindman168

theorem alignmentIntegerArrayArgument_difference {n : ℕ} {i : Fin n}
    (t : Fin n → ℕ) (M : ℕ) (ρ : AlignmentAddingPair n i → ℕ)
    (Δ : AlignmentAddingPair n i → ℤ) (T : Finset (Fin n))
    (p p0 : ℤ) (v u : AlignmentAddingPair n i → ℤ) :
    alignmentIntegerArrayArgument t M ρ Δ T p v u - (alignmentNaturalBlockProduct t T : ℤ) * p0 =
      (alignmentNaturalBlockProduct t T : ℤ) * (p - p0 + alignmentIntegerSlotShift ρ v) +
        (M : ℤ) * alignmentIntegerArrayProgression Δ T u := by
  unfold alignmentIntegerArrayArgument
  ring

theorem alignmentIntegerArrayArgument_interval_stable {n : ℕ} {i : Fin n}
    (t : Fin n → ℕ) (M : ℕ) (ρ : AlignmentAddingPair n i → ℕ)
    (Δ : AlignmentAddingPair n i → ℤ) (T : Finset (Fin n))
    (p p0 : ℤ) (v u : AlignmentAddingPair n i → ℤ) (H R S U : ℕ) (hH : 0 < H)
    (hp : |p - p0| ≤ (R : ℤ)) (hv : |alignmentIntegerSlotShift ρ v| ≤ (S : ℤ))
    (hu : |(M : ℤ) * alignmentIntegerArrayProgression Δ T u| ≤ (U : ℤ))
    (hy : intervalInteriorRoot H (alignmentNaturalBlockProduct t T * (R + S) + U)
      ((alignmentNaturalBlockProduct t T : ℤ) * p0)) :
    alignmentIntegerArrayArgument t M ρ Δ T p v u / (H : ℤ) =
      ((alignmentNaturalBlockProduct t T : ℤ) * p0) / (H : ℤ) := by
  have hb : |alignmentIntegerArrayArgument t M ρ Δ T p v u -
      (alignmentNaturalBlockProduct t T : ℤ) * p0| ≤
      (alignmentNaturalBlockProduct t T * (R + S) + U : ℕ) := by
    rw [alignmentIntegerArrayArgument_difference]
    calc
      _ ≤ |(alignmentNaturalBlockProduct t T : ℤ) * (p - p0 + alignmentIntegerSlotShift ρ v)| +
          |(M : ℤ) * alignmentIntegerArrayProgression Δ T u| := abs_add_le _ _
      _ ≤ (alignmentNaturalBlockProduct t T : ℤ) * (R + S) + U := by
        rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
        exact add_le_add (mul_le_mul_of_nonneg_left
          ((abs_add_le _ _).trans (add_le_add hp hv)) (Int.natCast_nonneg _)) hu
      _ = _ := by push_cast; rfl
  have hh := intervalInteriorRoot_shift_quotient H _ hH _
    (alignmentIntegerArrayArgument t M ρ Δ T p v u - (alignmentNaturalBlockProduct t T : ℤ) * p0) hy hb
  simpa only [add_sub_cancel] using hh

end Hindman168
