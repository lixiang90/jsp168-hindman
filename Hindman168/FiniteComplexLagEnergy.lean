import Hindman168.FinitePositiveLagReindex
import Hindman168.FiniteComplexSetMean
import Mathlib.Data.Complex.BigOperators

namespace Hindman168
open scoped BigOperators Classical

noncomputable def finiteComplexLagCorrelation (f : ℕ → ℂ) (N h : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N-h), f (n+h)*star (f n)

theorem finite_complex_sum_square_triangle (f : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, f n‖^2 =
      (∑ n ∈ Finset.range N, ‖f n‖^2) +
        2*∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j, (f j*star (f i)).re := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ih]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have he : ((∑ n ∈ Finset.range N, f n)*star (f N)).re =
        ∑ i ∈ Finset.range N, (f N*star (f i)).re := by
      rw [Finset.sum_mul, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    rw [← Complex.star_def, he]
    ring

/-- Exact actual finite energy decomposition into diagonal energy and real
positive-lag correlations. -/
theorem finite_complex_positive_lag_energy (f : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, f n‖^2 =
      (∑ n ∈ Finset.range N, ‖f n‖^2) +
        2*∑ h ∈ positiveNaturalLags N, (finiteComplexLagCorrelation f N h).re := by
  rw [finite_complex_sum_square_triangle, finite_positive_lag_reindex]
  simp only [finiteComplexLagCorrelation, Complex.re_sum]

theorem finite_complex_lag_correlation_norm_bound (f : ℕ → ℂ) (N h : ℕ)
    (hf : ∀ n < N, ‖f n‖ ≤ 1) :
    ‖finiteComplexLagCorrelation f N h‖ ≤ (N-h : ℕ) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.range (N-h), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_range.mp hn
      have hnl : n < N := by omega
      have hnh : n+h < N := by omega
      rw [norm_mul, norm_star]
      exact mul_le_one₀ (hf _ hnh) (norm_nonneg _) (hf _ hnl)
    _ = _ := by simp

theorem finite_complex_lag_correlation_zero_of_large_lag (f : ℕ → ℂ) (N h : ℕ)
    (hh : N ≤ h) : finiteComplexLagCorrelation f N h = 0 := by
  simp only [finiteComplexLagCorrelation, Nat.sub_eq_zero_of_le hh,
    Finset.range_zero, Finset.sum_empty]

end Hindman168
