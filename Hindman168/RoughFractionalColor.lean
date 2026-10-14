import Hindman168.RoughConstantTermModel

namespace Hindman168
open Polynomial

noncomputable def roughFractionalColor (q : ℕ) (x : ℝ) : Fin (2 ^ (q + 2)) :=
  ⟨⌊((2 ^ (q + 2) : ℕ) : ℝ) * Int.fract x⌋₊, by
    apply (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg x))).mpr
    have hp : (0 : ℝ) < ((2 ^ (q + 2) : ℕ) : ℝ) := by positivity
    simpa only [mul_one] using mul_lt_mul_of_pos_left (Int.fract_lt_one x) hp⟩

theorem roughFractionalColor_interval (q : ℕ) (x : ℝ) (c : Fin (2 ^ (q + 2)))
    (h : roughFractionalColor q x = c) :
    (c.val : ℝ) / (2 : ℝ) ^ (q + 2) ≤ Int.fract x ∧
      Int.fract x ≤ (c.val : ℝ) / (2 : ℝ) ^ (q + 2) + ((2 : ℝ) ^ (q + 2))⁻¹ := by
  have hc := congrArg Fin.val h
  change ⌊((2 ^ (q + 2) : ℕ) : ℝ) * Int.fract x⌋₊ = c.val at hc
  have hl := Nat.floor_le (mul_nonneg (Nat.cast_nonneg (2 ^ (q + 2))) (Int.fract_nonneg x))
  have hu := Nat.lt_floor_add_one (((2 ^ (q + 2) : ℕ) : ℝ) * Int.fract x)
  rw [hc] at hl hu
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hl hu
  have hp : (0 : ℝ) < 2 ^ (q + 2) := by positivity
  constructor
  · apply (div_le_iff₀ hp).mpr
    simpa only [mul_comm] using hl
  · calc
      Int.fract x ≤ ((c.val : ℝ) + 1) / 2 ^ (q + 2) := by
        apply (le_div_iff₀ hp).mpr
        simpa only [mul_comm] using hu.le
      _ = _ := by rw [add_div, one_div]

theorem rough_fractional_color_width (q : ℕ) :
    (2 : ℝ) ^ (q + 1) * ((2 : ℝ) ^ (q + 2))⁻¹ < 1 := by
  have hpow : (2 : ℝ) ^ (q + 2) = 2 ^ (q + 1) * 2 := by
    rw [show q + 2 = (q + 1) + 1 by omega, pow_succ]
  have heq : (2 : ℝ) ^ (q + 1) * ((2 : ℝ) ^ (q + 2))⁻¹ = 1 / 2 := by
    rw [hpow]
    field_simp
  rw [heq]
  norm_num

theorem rough_constant_term_model_of_one_color (P : ℝ[X]) (q H : ℕ)
    (hP : P.natDegree ≤ q) (c : Fin (2 ^ (q + 2)))
    (hc : ∀ z : ℕ, z < H → roughFractionalColor q (P.eval (z : ℝ)) = c) :
    ∃ M : ℚ[X], M.natDegree ≤ q ∧
      (∀ j, (M.coeff j).den ∣ q.factorial) ∧
      ∀ z : ℕ, z < H → M.eval (z : ℚ) = (⌊P.eval (z : ℝ)⌋ : ℚ) ∧
        0 ≤ P.eval (z : ℝ) - ((M.eval (z : ℚ) : ℚ) : ℝ) ∧
        P.eval (z : ℝ) - ((M.eval (z : ℚ) : ℚ) : ℝ) < 1 := by
  apply rough_constant_term_model P q H hP ((c.val : ℝ) / (2 : ℝ) ^ (q + 2))
    ((2 : ℝ) ^ (q + 2))⁻¹ (rough_fractional_color_width q)
  intro z hz
  exact roughFractionalColor_interval q (P.eval (z : ℝ)) c (hc z hz)

end Hindman168
