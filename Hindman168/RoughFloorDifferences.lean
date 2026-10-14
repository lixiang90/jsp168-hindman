import Hindman168.RoughForwardDifferences
import Mathlib.Algebra.Order.Floor.Ring

namespace Hindman168
open Polynomial
open scoped fwdDiff

theorem rough_floor_difference_zero (P : ℝ[X]) (q z : ℕ) (hP : P.natDegree ≤ q)
    (a delta : ℝ) (hsmall : (2 : ℝ) ^ (q + 1) * delta < 1)
    (hbin : ∀ j, j ≤ q + 1 → a ≤ Int.fract (P.eval ((z + j : ℕ) : ℝ)) ∧
      Int.fract (P.eval ((z + j : ℕ) : ℝ)) ≤ a + delta) :
    (Δ_[1]^[q + 1] (fun j : ℕ => ⌊P.eval (j : ℝ)⌋)) z = 0 := by
  let f : ℕ → ℤ := fun j => ⌊P.eval (j : ℝ)⌋
  let g : ℕ → ℝ := fun j => Int.fract (P.eval (j : ℝ)) - a
  have hdecomp : (fun j : ℕ => P.eval (j : ℝ)) =
      ((fun j => (f j : ℝ)) + (fun _ => a)) + g := by
    funext j
    dsimp [f, g]
    have hh := Int.floor_add_fract (P.eval (j : ℝ))
    linarith
  have hz := rough_fwdDiff_polynomial_zero P q z hP
  rw [hdecomp, fwdDiff_iter_add, fwdDiff_iter_add,
    rough_fwdDiff_const a (q + 1) (by omega)] at hz
  simp only [Pi.add_apply, add_zero] at hz
  have hb : |(Δ_[1]^[q + 1] g) z| ≤ 2 ^ (q + 1) * delta := by
    apply rough_fwdDiff_bound
    intro j hj
    dsimp [g]
    rw [abs_of_nonneg (sub_nonneg.mpr (hbin j hj).1)]
    linarith [(hbin j hj).2]
  apply rough_integer_eq_zero_of_abs_lt_one
  rw [rough_fwdDiff_intCast]
  have heq : (Δ_[1]^[q + 1] (fun j => (f j : ℝ))) z = -(Δ_[1]^[q + 1] g) z := by linarith
  change |(Δ_[1]^[q + 1] (fun j => (f j : ℝ))) z| < 1
  rw [heq, abs_neg]
  exact hb.trans_lt hsmall

theorem rough_floor_differences_on_interval (P : ℝ[X]) (q H : ℕ) (hP : P.natDegree ≤ q)
    (a delta : ℝ) (hsmall : (2 : ℝ) ^ (q + 1) * delta < 1)
    (hbin : ∀ j : ℕ, j < H → a ≤ Int.fract (P.eval (j : ℝ)) ∧
      Int.fract (P.eval (j : ℝ)) ≤ a + delta) :
    ∀ z : ℕ, z + q + 1 < H →
      (Δ_[1]^[q + 1] (fun j : ℕ => ⌊P.eval (j : ℝ)⌋)) z = 0 := by
  intro z hz
  apply rough_floor_difference_zero P q z hP a delta hsmall
  intro j hj
  exact hbin (z + j) (by omega)

end Hindman168
