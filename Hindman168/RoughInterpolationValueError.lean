import Hindman168.RoughInterpolationIntegerValues

namespace Hindman168

theorem rough_interpolation_near_integer_bound {R T b C eps : ℝ}
    (hinterp : |R - T| ≤ C * eps) (hnear : |T - b| ≤ eps) :
    |R - b| ≤ (C + 1) * eps := by
  calc
    |R - b| ≤ |R - T| + |T - b| := abs_sub_le R T b
    _ ≤ C * eps + eps := add_le_add hinterp hnear
    _ = _ := by ring

theorem rough_interpolation_divided_error {S Z t theta R M C : ℝ}
    (hS : 0 < S) (hSt : S ≤ t) (e : ℕ)
    (hfactor : R = t ^ e * M)
    (herror : |t ^ e * theta - R| ≤ C * (S / Z) ^ e) :
    |theta - M| ≤ C * Z⁻¹ ^ e := by
  have ht : 0 < t := hS.trans_le hSt
  have he : t ^ e * |theta - M| ≤ C * (S / Z) ^ e := by
    rwa [hfactor, ← mul_sub, abs_mul, abs_of_pos (pow_pos ht e)] at herror
  have hpow : S ^ e ≤ t ^ e := by gcongr
  have hbound : S ^ e * |theta - M| ≤ C * (S / Z) ^ e :=
    (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)).trans he
  apply (mul_le_mul_iff_right₀ (pow_pos hS e)).mp
  have hid : C * (S / Z) ^ e = (C * Z⁻¹ ^ e) * S ^ e := by
    rw [div_eq_mul_inv, mul_pow]
    ring
  rw [hid, mul_comm (S ^ e)] at hbound
  simpa only [mul_comm] using hbound

end Hindman168
