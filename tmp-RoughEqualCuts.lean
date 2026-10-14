import Hindman168.RoughFiniteBoxWeightComparison

namespace Hindman168

def roughEqualCut (A B : ℤ) (N i : ℕ) : ℤ := A + (B - A) * (i : ℤ) / (N : ℤ)

theorem rough_equal_cut_zero (A B : ℤ) (N : ℕ) : roughEqualCut A B N 0 = A := by
  simp [roughEqualCut]

theorem rough_equal_cut_end (A B : ℤ) (N : ℕ) (hN : 0 < N) :
    roughEqualCut A B N N = B := by
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold roughEqualCut
  rw [mul_comm (B - A), Int.mul_ediv_cancel_left _ hNz]
  omega

theorem rough_equal_cut_side_error (A B : ℤ) (N i : ℕ) (hN : 0 < N) :
    |((roughEqualCut A B N (i + 1) : ℝ) - roughEqualCut A B N i) -
      ((B : ℝ) - A) / N| ≤ 1 := by
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let L : ℤ := B - A
  let x : ℤ := L * (i : ℤ)
  let y : ℤ := L * ((i : ℤ) + 1)
  have hx := Int.emod_add_mul_ediv x (N : ℤ)
  have hy := Int.emod_add_mul_ediv y (N : ℤ)
  have hx0 := Int.emod_nonneg x hNz.ne'
  have hy0 := Int.emod_nonneg y hNz.ne'
  have hxN := Int.emod_lt_of_pos x hNz
  have hyN := Int.emod_lt_of_pos y hNz
  have he : (N : ℤ) * (y / N - x / N) - L = x % N - y % N := by
    have hxy : y - x = L := by dsimp [x, y]; ring
    nlinarith
  have hl : -(N : ℤ) ≤ (N : ℤ) * (y / N - x / N) - L := by omega
  have hu : (N : ℤ) * (y / N - x / N) - L ≤ N := by omega
  have hlr : -(N : ℝ) ≤ (N : ℝ) * ((y / N : ℤ) - (x / N : ℤ)) - L := by exact_mod_cast hl
  have hur : (N : ℝ) * ((y / N : ℤ) - (x / N : ℤ)) - L ≤ N := by exact_mod_cast hu
  have hcut : ((roughEqualCut A B N (i + 1) : ℝ) - roughEqualCut A B N i) =
      ((y / N : ℤ) : ℝ) - ((x / N : ℤ) : ℝ) := by
    simp only [roughEqualCut, x, y, L, Nat.cast_add, Nat.cast_one, Int.cast_add]
    ring
  rw [hcut, abs_le]
  constructor
  · dsimp [L] at hlr
    push_cast at hlr
    have hh : ((B : ℝ) - A - N) / N ≤ ((y / N : ℤ) : ℝ) - ((x / N : ℤ) : ℝ) :=
      (div_le_iff₀ hNr).mpr (by nlinarith [hlr])
    have heq : ((B : ℝ) - A - N) / N = ((B : ℝ) - A) / N - 1 := by field_simp
    rw [heq] at hh
    linarith
  · have hh : (((y / N : ℤ) : ℝ) - ((x / N : ℤ) : ℝ)) * N ≤ (B : ℝ) - A + N := by
      dsimp [L] at hur
      push_cast at hur
      nlinarith
    have hd := (le_div_iff₀ hNr).mpr hh
    have he : ((B : ℝ) - A + N) / N = ((B : ℝ) - A) / N + 1 := by field_simp
    rw [he] at hd
    linarith

end Hindman168
