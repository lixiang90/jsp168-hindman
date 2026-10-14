import Hindman168.RoughSmoothDenominatorSupport
import Hindman168.RoughInterpolationExactnessScale

namespace Hindman168
open Polynomial Filter
open scoped Topology

theorem rough_cleared_polynomial_integer_eval_lattice (R : ℚ[X]) (P : ℤ[X]) (D : ℕ)
    (hclear : C (D : ℚ) * R = P.map (Int.castRingHom ℚ)) (z : ℤ) :
    ∃ a : ℤ, (D : ℚ) * R.eval (z : ℚ) = a := by
  simpa only [one_pow, mul_one, Nat.cast_one, div_one, Function.iterate_zero_apply] using
    rough_polynomial_derivative_clear R P D P.natDegree hclear le_rfl z 1 (by omega) 0

theorem rough_cleared_polynomial_near_integer (R : ℚ[X]) (P : ℤ[X]) (D : ℕ)
    (hD : 0 < D) (hclear : C (D : ℚ) * R = P.map (Int.castRingHom ℚ))
    (z b : ℤ) (hnear : |((R.eval (z : ℚ) : ℚ) : ℝ) - b| < 1 / (D : ℝ)) :
    R.eval (z : ℚ) = b := by
  obtain ⟨a, ha⟩ := rough_cleared_polynomial_integer_eval_lattice R P D hclear z
  have he := rough_lattice_near_integer hD
    (x := ((R.eval (z : ℚ) : ℚ) : ℝ))
    ⟨a, by exact_mod_cast ha⟩ b hnear
  exact_mod_cast he

theorem rough_interpolation_quotient_integer_eventually
    {S Z : ℕ → ℝ} (hg : PowerDominates atTop Z S)
    (hS : ∀ᶠ w in atTop, 1 ≤ S w) (hZ : ∀ᶠ w in atTop, 0 ≤ Z w)
    (D e : ℕ) (hD : 0 < D) (he : 0 < e) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ w in atTop, ∀ (R M : ℚ[X]) (P : ℤ[X]) (t z : ℤ) (m tau : ℕ),
      m ≠ 0 → (∀ p, p.Prime → p ∣ m → p ≤ w) →
      (tau : ℤ) = t + (m : ℤ) * z → (primorial w).Coprime tau →
      Polynomial.C (D : ℚ) * R = P.map (Int.castRingHom ℚ) →
      R = (Polynomial.C (t : ℚ) + Polynomial.C (m : ℚ) * X) ^ e * M →
      (∃ b : ℤ, |((R.eval (z : ℚ) : ℚ) : ℝ) - b| ≤ K * (S w / Z w) ^ e) →
      ∃ a : ℤ, M.eval (z : ℚ) = a := by
  have hsmall := rough_interpolation_error_eventually hg hS hZ K hK D
    (by exact_mod_cast hD) 0 e he
  filter_upwards [hsmall, eventually_ge_atTop D] with
    w hw hDw R M P t z m tau hm hmW htau ht hclear hfactor hnear
  apply rough_smooth_quotient_integer_eval w D w m m e
    (fixed_integer_dvd_primorial_power hD.ne' hDw) hm
    (rough_smooth_integer_dvd_primorial_power hm hmW) t z tau htau ht R M P hclear hfactor
  obtain ⟨b, hb⟩ := hnear
  refine ⟨b, rough_cleared_polynomial_near_integer R P D hD hclear z b ?_⟩
  apply hb.trans_lt
  simpa only [pow_zero, mul_one] using hw

end Hindman168
