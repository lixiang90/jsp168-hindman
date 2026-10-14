import Hindman168.AlignmentCubeCoordinateBounds
import Hindman168.AlignmentShortCutoffGeometry

namespace Hindman168
open scoped BigOperators

noncomputable def alignmentCubeScale {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ) : ℝ :=
  (alignmentShortBinVolume F w i T x : ℝ) / (F.modulus w : ℝ)

theorem alignment_actual_cube_base_bound {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (hx : ∀ j ∈ T, 0 < x j)
    (hR : 0 < alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
    (p ell : ℤ) (K : ℕ)
    (hp : |p - (x i : ℤ)| ≤ (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ))
    (hell : |(F.modulus w : ℤ) * ell| ≤
      (K : ℤ) * (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ)) :
    |(alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct x T) p
      ((alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)) ell : ℝ)| ≤
      ((2 : ℝ) ^ T.card * (K + 1) + 1) * alignmentCubeScale F w i T x + 1 := by
  have hd := (binaryDyadicProduct_bounds T x hx).2
  have hv : 0 < alignmentShortBinVolume F w i T x := by
    unfold alignmentShortBinVolume
    positivity
  have hb := (sameNaturalShortBin_iff hv
    (alignmentNaturalBlockProduct x T * x i) (alignmentNaturalBlockProduct x T * x i)).mp rfl
  have hbin : |(alignmentNaturalBlockProduct x T : ℤ) * (x i : ℤ) -
      (alignmentShortBinStart F w i T x : ℤ)| ≤
        ((∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ) : ℤ) *
          (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ) := by
    have hlo : (alignmentShortBinStart F w i T x : ℤ) ≤
        (alignmentNaturalBlockProduct x T : ℤ) * (x i : ℤ) := by exact_mod_cast hb.1
    have hhi : (alignmentNaturalBlockProduct x T : ℤ) * (x i : ℤ) <
        (alignmentShortBinStart F w i T x : ℤ) + (alignmentShortBinVolume F w i T x : ℤ) := by
      exact_mod_cast hb.2
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    unfold alignmentShortBinVolume at hhi
    simp only [Nat.cast_mul] at hhi
    omega
  have h := alignmentCubeBase_normalized_bound (F.modulus w) (alignmentNaturalBlockProduct x T)
    p (alignmentShortBinStart F w i T x) ell (x i)
    (∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ)
    (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (2 ^ T.card : ℕ) K
    (by exact_mod_cast (F.modulus w).pos) (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast hd) hp hell hbin
  simpa only [Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat, Int.cast_pow, Int.cast_ofNat,
    alignmentCubeScale, alignmentShortBinVolume, Nat.cast_mul] using h

theorem alignment_actual_cube_increment_bound {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (hx : ∀ j ∈ T, 0 < x j) (ell : ℤ) (K : ℕ)
    (hell : |(F.modulus w : ℤ) * ell| ≤
      (K : ℤ) * (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ)) :
    |((alignmentNaturalBlockProduct x T : ℤ) * ell : ℤ)| ≤
      (2 : ℝ) ^ T.card * K * alignmentCubeScale F w i T x := by
  have hd := (binaryDyadicProduct_bounds T x hx).2
  have h := alignmentCubeIncrement_scale_bound (F.modulus w) (alignmentNaturalBlockProduct x T)
    ell (∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ)
    (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (2 ^ T.card : ℕ) K
    (by exact_mod_cast (F.modulus w).pos) (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast hd) (by exact_mod_cast hell)
  simpa only [alignmentCubeScale, alignmentShortBinVolume, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, Int.cast_abs, Int.cast_mul, Int.cast_natCast] using h

theorem alignmentCubeScale_ge_one {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (hR : 0 < alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) :
    1 ≤ alignmentCubeScale F w i T x := by
  have hd : (F.modulus w : ℕ) ∣ alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) :=
    ⟨Nat.sqrt (F.gap w i.val) / (F.modulus w : ℕ), rfl⟩
  have hm := Nat.le_of_dvd hR hd
  have ha : 1 ≤ (∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ) := by
    have h : 0 < (∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ) := by positivity
    omega
  have hv : (F.modulus w : ℕ) ≤ alignmentShortBinVolume F w i T x := by
    unfold alignmentShortBinVolume
    calc
      _ ≤ alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) := hm
      _ = 1 * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ ha
  unfold alignmentCubeScale
  apply (le_div_iff₀ (by exact_mod_cast (F.modulus w).pos : (0 : ℝ) < F.modulus w)).mpr
  simpa only [one_mul] using (show (F.modulus w : ℝ) ≤ alignmentShortBinVolume F w i T x from by
    exact_mod_cast hv)

theorem alignment_actual_cube_base_fixed_multiple {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (hx : ∀ j ∈ T, 0 < x j)
    (hR : 0 < alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
    (p ell : ℤ) (K : ℕ)
    (hp : |p - (x i : ℤ)| ≤ (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ))
    (hell : |(F.modulus w : ℤ) * ell| ≤
      (K : ℤ) * (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ)) :
    |(alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct x T) p
      ((alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)) ell : ℝ)| ≤
      ((2 : ℝ) ^ T.card * (K + 1) + 2) * alignmentCubeScale F w i T x := by
  have h := alignment_actual_cube_base_bound F w i T x hx hR p ell K hp hell
  have hz := alignmentCubeScale_ge_one F w i T x hR
  nlinarith

end Hindman168
