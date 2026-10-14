import Hindman168.AlignmentAffineIntervalClasses
import Hindman168.AlignmentActualCubeBounds

namespace Hindman168
open scoped BigOperators

theorem alignment_scaled_interval_length (M t a R C c K L U : ℝ)
    (hM : 0 < M) (ha : 0 ≤ a) (hR : 0 ≤ R) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hat : a ≤ t) (htC : t ≤ C * a)
    (hlo : c * R ≤ M * (U - L)) (hhi : M * (U - L) ≤ K * R) :
    c * (a * R / M) ≤ t * (U - L) ∧ t * (U - L) ≤ C * K * (a * R / M) := by
  have hlen : 0 ≤ M * (U - L) := (mul_nonneg hc hR).trans hlo
  have ht := ha.trans hat
  have hl := mul_le_mul hlo hat ha hlen
  have hu := mul_le_mul hhi htC ht (mul_nonneg hK hR)
  constructor
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hM).mpr
    nlinarith [hl]
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hM).mpr
    nlinarith [hu]

theorem alignment_actual_cube_side_lengths {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (hx : ∀ j ∈ T, 0 < x j) (p Y A B : ℤ) (c K : ℝ)
    (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hlo : c * (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ) ≤
      (F.modulus w : ℝ) * ((B : ℝ) - A))
    (hhi : (F.modulus w : ℝ) * ((B : ℝ) - A) ≤
      K * (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ)) :
    c * alignmentCubeScale F w i T x ≤
      ((alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct x T) p Y B -
        alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct x T) p Y A : ℤ) : ℝ) ∧
      ((alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct x T) p Y B -
        alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct x T) p Y A : ℤ) : ℝ) ≤
          (2 : ℝ) ^ T.card * K * alignmentCubeScale F w i T x := by
  have hd := binaryDyadicProduct_bounds T x hx
  have h := alignment_scaled_interval_length (F.modulus w) (alignmentNaturalBlockProduct x T)
    (∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ)
    (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (2 ^ T.card : ℕ) c K A B
    (by exact_mod_cast (F.modulus w).pos) (by positivity) (by positivity) hc hK
    (by exact_mod_cast hd.1) (by exact_mod_cast hd.2) hlo hhi
  rw [alignmentCubeBase_interval_length]
  simpa only [alignmentCubeScale, alignmentShortBinVolume, Nat.cast_mul, Int.cast_mul,
    Int.cast_sub, Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat] using h

theorem alignment_retained_step_interval (q a L U y : ℝ) (hq : 0 < q) :
    (L ≤ a + q * y ∧ a + q * y < U) ↔ ((L - a) / q ≤ y ∧ y < (U - a) / q) := by
  rw [div_le_iff₀ hq, lt_div_iff₀ hq]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

theorem alignment_retained_step_length (q a L U Z c C : ℝ) (hq : 0 < q)
    (hlo : c * Z ≤ U - L) (hhi : U - L ≤ C * Z) :
    c * (Z / q) ≤ (U - a) / q - (L - a) / q ∧
      (U - a) / q - (L - a) / q ≤ C * (Z / q) := by
  have he : (U - a) / q - (L - a) / q = (U - L) / q := by ring
  rw [he, ← mul_div_assoc, ← mul_div_assoc]
  exact ⟨div_le_div_of_nonneg_right hlo hq.le, div_le_div_of_nonneg_right hhi hq.le⟩

end Hindman168
