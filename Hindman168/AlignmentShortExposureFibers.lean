import Hindman168.AlignmentDyadicExposureGeometry

namespace Hindman168
open scoped BigOperators Classical

theorem alignmentShortExposureKey_iff {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x y : Fin n → ℕ) :
    alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y ↔
      alignmentRawExposure i ((F.modulus w : ℕ) * (primorial w) ^ w) T x y ∧
      (∀ j ∈ T, Nat.log2 (x j) = Nat.log2 (y j)) ∧
      Nat.ModEq (F.modulus w : ℕ) (x i) (y i) ∧
      (alignmentNaturalBlockProduct x T * x i) /
        ((∏ j ∈ T, 2 ^ Nat.log2 (x j)) * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) =
      (alignmentNaturalBlockProduct y T * y i) /
        ((∏ j ∈ T, 2 ^ Nat.log2 (x j)) * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) := by
  constructor
  · intro h
    exact ⟨alignmentShortExposureKey_rawExposure F w i T h,
      alignmentShortExposureKey_dyadic_eq F w i T h,
      alignmentShortExposureKey_pivot_residue F w i T h,
      alignmentShortExposureKey_product_bin F w i T h⟩
  · rintro ⟨hraw, hdy, hp, hb⟩
    have hprod : (∏ j ∈ T, 2 ^ Nat.log2 (x j)) = ∏ j ∈ T, 2 ^ Nat.log2 (y j) :=
      Finset.prod_congr rfl (fun j hj => congrArg (fun k => 2 ^ k) (hdy j hj))
    unfold alignmentShortExposureKey
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    all_goals dsimp only
    · funext j
      split_ifs with hj
      · exact hraw.1 j hj.1 hj.2
      · rfl
    · funext j
      split_ifs with hj
      · exact hraw.2 j hj
      · rfl
    · funext j
      split_ifs with hj
      · exact hdy j hj
      · rfl
    · exact hp
    · simpa only [hprod] using hb

theorem alignmentShortExposureKey_window_iff {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x y : Fin n → ℕ)
    (hy : ∀ j ∈ T, 0 < y j) :
    alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y ↔
      (∀ j, j < i → j ∉ T → x j = y j) ∧
      (∀ j ∈ T, y j ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j)) ∧
      Nat.ModEq (F.modulus w : ℕ) (x i) (y i) ∧
      (alignmentNaturalBlockProduct x T * x i) /
        ((∏ j ∈ T, 2 ^ Nat.log2 (x j)) * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) =
      (alignmentNaturalBlockProduct y T * y i) /
        ((∏ j ∈ T, 2 ^ Nat.log2 (x j)) * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) := by
  rw [alignmentShortExposureKey_iff]
  constructor
  · rintro ⟨hraw, hdy, hp, hb⟩
    refine ⟨hraw.1, ?_, hp, hb⟩
    intro j hj
    exact (binaryDyadicResidueWindow_mem (hy j hj)).mpr ⟨(hdy j hj).symm, (hraw.2 j hj).symm⟩
  · rintro ⟨hout, hwin, hp, hb⟩
    have hh := fun j hj => (binaryDyadicResidueWindow_mem (hy j hj)).mp (hwin j hj)
    exact ⟨⟨hout, fun j hj => (hh j hj).2.symm⟩, fun j hj => (hh j hj).1.symm, hp, hb⟩

end Hindman168
