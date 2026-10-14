import Hindman168.UnitCirclePolynomialDiscrepancy

namespace Hindman168
open Polynomial
open scoped BigOperators Classical Topology

theorem unit_circle_polynomial_fourier_large_frequency (p : ℝ[X]) (N : ℕ) (hN : 0 < N)
    (c : ℤ →₀ ℂ) (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (hbudget : ∑ k ∈ c.support, ‖c k‖ ≤ B)
    (hlarge : δ/2 ≤ ‖unitCirclePolynomialDiscrepancy p N
      (c.sum (fun k a => a • (fourier k : C(UnitAddCircle, ℂ))))‖) :
    ∃ k ∈ c.support, k ≠ 0 ∧ δ/(4*B) ≤ ‖unitCirclePolynomialDiscrepancy p N (fourier k)‖ := by
  by_contra! h
  have hphase : ∀ k ∈ c.support, ‖unitCirclePolynomialDiscrepancy p N (fourier k)‖ ≤ δ/(4*B) := by
    intro k hk
    by_cases hz : k=0
    · rw [hz, unit_circle_polynomial_zero_fourier_discrepancy p N hN, norm_zero]
      positivity
    · exact (h k hk hz).le
  have heq : unitCirclePolynomialDiscrepancy p N
      (c.sum (fun k a => a • (fourier k : C(UnitAddCircle, ℂ)))) =
      ∑ k ∈ c.support, c k*unitCirclePolynomialDiscrepancy p N (fourier k) := by
    rw [Finsupp.sum, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hb : ‖unitCirclePolynomialDiscrepancy p N
      (c.sum (fun k a => a • (fourier k : C(UnitAddCircle, ℂ))))‖ ≤ δ/4 := by
    rw [heq]
    calc
      _ ≤ ∑ k ∈ c.support, ‖c k*unitCirclePolynomialDiscrepancy p N (fourier k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ c.support, ‖c k‖*(δ/(4*B)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hphase k hk) (norm_nonneg _)
      _ = (∑ k ∈ c.support, ‖c k‖)*(δ/(4*B)) := by rw [Finset.sum_mul]
      _ ≤ B*(δ/(4*B)) := mul_le_mul_of_nonneg_right hbudget (by positivity)
      _ = δ/4 := by field_simp
  linarith

end Hindman168
