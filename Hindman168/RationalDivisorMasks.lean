import Hindman168.DivisorMaskExpansion
import Hindman168.SmoothAbsorption
import Mathlib.Data.ZMod.Basic

/-!
# Original divisor masks on integer-valued rational arguments

Rational divisibility means an integer multiple of the divisor. This
agrees exactly with the original integer mask. Clearing a denominator
preserves the mask when it is coprime to every supported divisor and
the original argument is an integer. Integrality is not discarded.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def rationalDivisorMask (ρ : Mass ℕ) (y : ℚ) : ℝ :=
  expectation ρ (fun k => if ∃ z : ℤ, y = (k : ℚ) * z then (k : ℝ) else 0)

theorem rational_integer_multiple_iff (k : ℕ) (z : ℤ) :
    (∃ t : ℤ, (z : ℚ) = (k : ℚ) * t) ↔ (k : ℤ) ∣ z := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by exact_mod_cast ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by exact_mod_cast ht⟩

theorem rationalDivisorMask_intCast (ρ : Mass ℕ) (z : ℤ) :
    rationalDivisorMask ρ (z : ℚ) = integerDivisorMask ρ z := by
  simp only [rationalDivisorMask, rational_integer_multiple_iff, integerDivisorMask_expectation]

theorem integer_dvd_unit_scaled_iff {a k : ℕ} (h : a.Coprime k) (z : ℤ) :
    (k : ℤ) ∣ (a : ℤ) * z ↔ (k : ℤ) ∣ z := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    Int.cast_mul, Int.cast_natCast, ← ZMod.coe_unitOfCoprime a h, Units.mul_right_eq_zero]

theorem integerDivisorMask_unit_scaled (ρ : Mass ℕ) (a : ℕ) (z : ℤ)
    (h : ∀ k ∈ ρ.support, a.Coprime k) :
    integerDivisorMask ρ ((a : ℤ) * z) = integerDivisorMask ρ z := by
  unfold integerDivisorMask
  apply Finset.sum_congr rfl
  intro k hk
  simp only [integer_dvd_unit_scaled_iff (h k hk)]

theorem rationalDivisorMask_clear (ρ : Mass ℕ) (a : ℕ) (y : ℚ) (b : ℤ)
    (hy : ∃ z : ℤ, y = (z : ℚ)) (hb : (a : ℚ) * y = (b : ℚ))
    (hunit : ∀ k ∈ ρ.support, a.Coprime k) :
    rationalDivisorMask ρ y = integerDivisorMask ρ b := by
  obtain ⟨z, rfl⟩ := hy
  have hz : (a : ℤ) * z = b := by exact_mod_cast hb
  rw [rationalDivisorMask_intCast, ← hz, integerDivisorMask_unit_scaled ρ a z hunit]

theorem rational_row_clear_eval {d : ℕ} (c : Fin d → ℚ) (a : ℕ) (b : Fin d → ℤ)
    (hb : ∀ j, (a : ℚ) * c j = (b j : ℚ)) (x : Fin d → ℤ) :
    (a : ℚ) * (∑ j, c j * (x j : ℚ)) = ((∑ j, b j * x j : ℤ) : ℚ) := by
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, hb j, Int.cast_mul]

theorem rational_row_exists_clear {d : ℕ} (c : Fin d → ℚ) :
    ∃ a : ℕ, 0 < a ∧ ∃ b : Fin d → ℤ, ∀ j, (a : ℚ) * c j = (b j : ℚ) := by
  let a := ∏ j, (c j).den
  have ha : 0 < a := Finset.prod_pos (fun j _ => (c j).den_pos)
  have hd (j : Fin d) : (c j).den ∣ a := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  choose b hb using (fun j => rational_mul_nat_integral (c j) (hd j))
  exact ⟨a, ha, b, hb⟩

theorem rational_row_mask_clear {d : ℕ} (ρ : Mass ℕ) (c : Fin d → ℚ)
    (a : ℕ) (b : Fin d → ℤ) (hb : ∀ j, (a : ℚ) * c j = (b j : ℚ))
    (x : Fin d → ℤ) (hx : ∃ z : ℤ, (∑ j, c j * (x j : ℚ)) = (z : ℚ))
    (hunit : ∀ k ∈ ρ.support, a.Coprime k) :
    rationalDivisorMask ρ (∑ j, c j * (x j : ℚ)) = integerDivisorMask ρ (∑ j, b j * x j) :=
  rationalDivisorMask_clear ρ a _ _ hx (rational_row_clear_eval c a b hb x) hunit

end Hindman168
