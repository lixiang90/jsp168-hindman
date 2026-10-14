import Hindman168.RoughMonomialOscillation

namespace Hindman168

/-- Actual power variation on a real interval of length L inside [0,N],
proved by normalizing the existing genuine power-oscillation inequality. -/
theorem normalized_real_power_variation (x y N L : ℝ) (d : ℕ) (hN : 0 < N)
    (hL : 0 ≤ L) (hx : |x| ≤ N) (hy : |y| ≤ N) (hxy : |x-y| ≤ L) :
    |x^d-y^d| ≤ (d : ℝ)*(L/N)*N^d := by
  have hxn : |x/N| ≤ 1 := by rw [abs_div, abs_of_pos hN]; exact (div_le_one hN).mpr hx
  have hyn : |y/N| ≤ 1 := by rw [abs_div, abs_of_pos hN]; exact (div_le_one hN).mpr hy
  have hdiff : |x/N-y/N| ≤ L/N := by
    rw [← sub_div, abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right hxy hN.le
  have hp := rough_power_oscillation (x/N) (y/N) 1 (L/N) d le_rfl
    (div_nonneg hL hN.le) hxn hyn hdiff
  simp only [one_pow, mul_one, div_pow, ← sub_div, abs_div, abs_of_pos (pow_pos hN d)] at hp
  exact (div_le_iff₀ (pow_pos hN d)).mp hp

theorem natural_progression_power_divisible (a q j d : ℕ) :
    (q : ℤ) ∣ ((a+q*j : ℕ) : ℤ)^d-(a : ℤ)^d := by
  have hd : (q : ℤ) ∣ ((a+q*j : ℕ) : ℤ)-(a : ℤ) := by
    refine ⟨(j : ℤ), ?_⟩
    push_cast
    ring
  exact hd.trans (sub_dvd_pow_sub_pow _ _ d)

end Hindman168
