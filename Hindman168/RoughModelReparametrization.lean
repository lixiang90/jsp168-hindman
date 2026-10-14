import Hindman168.RoughAffineDenominators
import Hindman168.RoughAffinePolynomial

namespace Hindman168
open Polynomial

theorem rough_coefficient_model_reparametrize {w N H q e a b : ℕ} {Z C : ℝ}
    {theta : ℝ[X]} {M : ℚ[X]} (h : RoughCoefficientModel w N q e Z C theta M)
    (hindex : ∀ z : ℕ, z < H → a + b * z < N) :
    RoughCoefficientModel w H q e Z C
      (theta.comp (Polynomial.C (a : ℝ) + Polynomial.C (b : ℝ) * X))
      (M.comp (Polynomial.C (a : ℚ) + Polynomial.C (b : ℚ) * X)) := by
  refine ⟨(rough_affine_comp_degree M (a : ℚ) (b : ℚ)).trans h.1, ?_, ?_⟩
  · simpa only [Int.cast_natCast] using rough_affine_comp_prime_support w M h.2.1 (a : ℤ) (b : ℤ)
  · intro z hz
    simpa only [rough_affine_comp_eval] using h.2.2 (a + b * z) (hindex z hz)

theorem rough_progression_reparametrize {w N H t m a b : ℕ} {S : ℝ}
    (hm : 0 < m) (hb : 0 < b) (hbw : b ≤ w)
    (hmsmooth : ∀ p, p.Prime → p ∣ m → p ≤ w)
    (hprog : ∀ z : ℕ, z < N → S ≤ (t + m * z : ℕ) ∧ (t + m * z : ℕ) < 2 * S)
    (hrough : ∀ z : ℕ, z < N → (primorial w).Coprime (t + m * z))
    (hindex : ∀ z : ℕ, z < H → a + b * z < N) :
    0 < m * b ∧ (∀ p, p.Prime → p ∣ m * b → p ≤ w) ∧
      (∀ z : ℕ, z < H → S ≤ ((t + m * a) + (m * b) * z : ℕ) ∧
        ((t + m * a) + (m * b) * z : ℕ) < 2 * S) ∧
      ∀ z : ℕ, z < H → (primorial w).Coprime ((t + m * a) + (m * b) * z) := by
  refine ⟨Nat.mul_pos hm hb, ?_, ?_, ?_⟩
  · intro p hp hpd
    rcases hp.dvd_mul.mp hpd with hpm | hpb
    · exact hmsmooth p hp hpm
    · exact (Nat.le_of_dvd hb hpb).trans hbw
  · intro z hz
    rw [show (t + m * a) + (m * b) * z = t + m * (a + b * z) by ring]
    exact hprog (a + b * z) (hindex z hz)
  · intro z hz
    rw [show (t + m * a) + (m * b) * z = t + m * (a + b * z) by ring]
    exact hrough (a + b * z) (hindex z hz)

end Hindman168
