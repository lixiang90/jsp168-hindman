import Hindman168.AlignmentActualCubeBounds
import Hindman168.AlignmentNumericalPolynomialBounds

namespace Hindman168

theorem alignment_retained_scale_power_bound (M q d a R V S eps : ℝ) (p : ℕ)
    (hM : 0 < M) (hq : 0 < q) (hd : 0 < d) (ha : 1 ≤ a)
    (hR : 0 ≤ R) (hV : 0 ≤ V) (hS : 0 ≤ S) (heps : 0 ≤ eps)
    (hMV : M ≤ V) (hqV : q ≤ V) (hSV : S ≤ V)
    (hsmall : d * V ^ (p + 2) ≤ eps * R) :
    S ^ p ≤ eps * ((a * R / M) / (d * q)) := by
  have hs : S ^ p ≤ V ^ p := pow_le_pow_left₀ hS hSV p
  have hmq : M * q ≤ V ^ 2 := by
    have h := mul_le_mul hMV hqV hq.le hV
    nlinarith
  have hprod : S ^ p * (M * (d * q)) ≤ d * V ^ (p + 2) := by
    have h := mul_le_mul hs hmq (mul_nonneg hM.le hq.le) (pow_nonneg hV p)
    have hd' := mul_le_mul_of_nonneg_left h hd.le
    rw [pow_add] at ⊢
    nlinarith [hd']
  have hlarge : eps * R ≤ eps * (a * R) := by
    have h := mul_le_mul_of_nonneg_right ha hR
    nlinarith [mul_le_mul_of_nonneg_left h heps]
  have hden : 0 < M * (d * q) := by positivity
  have he : eps * ((a * R / M) / (d * q)) = (eps * (a * R)) / (M * (d * q)) := by
    field_simp
  rw [he]
  exact (le_div_iff₀ hden).mpr (hprod.trans (hsmall.trans hlarge))

end Hindman168
