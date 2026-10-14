import Hindman168.FiniteComplexLagEnergy

namespace Hindman168
open scoped BigOperators Classical

/-- A true large finite mean forces a positive density of actual nonzero
lag correlations. The explicit large-N condition excludes the false short
interval positive-lag assertion. -/
theorem finite_complex_positive_lag_density (f : ℕ → ℂ) (N : ℕ) (hN : 0 < N)
    (hf : ∀ n < N, ‖f n‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (hlarge : 4 ≤ δ^2*(N : ℝ))
    (hmean : δ ≤ ‖finiteComplexSetMean (Finset.range N) f‖) :
    δ^2/8*(N : ℝ) ≤ ((positiveNaturalLags N).filter (fun h =>
      δ^2/8*(N : ℝ) ≤ ‖finiteComplexLagCorrelation f N h‖)).card := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : δ*(N : ℝ) ≤ ‖∑ n ∈ Finset.range N, f n‖ := by
    rw [finiteComplexSetMean, norm_div, Complex.norm_natCast, Finset.card_range] at hmean
    exact (le_div_iff₀ hNr).mp hmean
  have hsquare : δ^2*(N : ℝ)^2 ≤ ‖∑ n ∈ Finset.range N, f n‖^2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (by positivity) (norm_nonneg (∑ n ∈ Finset.range N, f n))).mpr hsum
  have hdiag : (∑ n ∈ Finset.range N, ‖f n‖^2) ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have h := hf n (Finset.mem_range.mp hn)
        nlinarith [norm_nonneg (f n)]
      _ = _ := by simp
  have hreal : (∑ h ∈ positiveNaturalLags N, (finiteComplexLagCorrelation f N h).re) ≤
      ∑ h ∈ positiveNaturalLags N, ‖finiteComplexLagCorrelation f N h‖ :=
    Finset.sum_le_sum (fun h _ => Complex.re_le_norm _)
  have henergy := finite_complex_positive_lag_energy f N
  let T := (positiveNaturalLags N).filter (fun h =>
    δ^2/8*(N : ℝ) ≤ ‖finiteComplexLagCorrelation f N h‖)
  have hc : ((positiveNaturalLags N).card : ℝ) ≤ N := by
    exact_mod_cast positive_natural_lags_card_le N
  have hbound : ∀ h, ‖finiteComplexLagCorrelation f N h‖ ≤ (N : ℝ) := by
    intro h
    exact (finite_complex_lag_correlation_norm_bound f N h hf).trans
      (by exact_mod_cast Nat.sub_le N h)
  have hupper : (∑ h ∈ positiveNaturalLags N, ‖finiteComplexLagCorrelation f N h‖) ≤
      (N : ℝ)*(δ^2/8*(N : ℝ))+(T.card : ℝ)*(N : ℝ) := by
    calc
      _ ≤ ∑ h ∈ positiveNaturalLags N, (δ^2/8*(N : ℝ)+
          if δ^2/8*(N : ℝ) ≤ ‖finiteComplexLagCorrelation f N h‖ then (N : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro h _
        by_cases hh : δ^2/8*(N : ℝ) ≤ ‖finiteComplexLagCorrelation f N h‖
        · rw [if_pos hh]
          have ht : 0 ≤ δ^2/8*(N : ℝ) := by positivity
          linarith [hbound h]
        · rw [if_neg hh, add_zero]
          exact (lt_of_not_ge hh).le
      _ = ((positiveNaturalLags N).card : ℝ)*(δ^2/8*(N : ℝ))+
          (T.card : ℝ)*(N : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, T]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hc
        (by positivity : 0 ≤ δ^2/8*(N : ℝ))) le_rfl
  have hlargeN := mul_le_mul_of_nonneg_right hlarge hNr.le
  change δ^2/8*(N : ℝ) ≤ (T.card : ℝ)
  apply (mul_le_mul_iff_right₀ hNr).mp
  nlinarith

theorem finite_complex_large_lag_remaining_length (f : ℕ → ℂ) (N h : ℕ)
    (hf : ∀ n < N, ‖f n‖ ≤ 1) (τ : ℝ)
    (hcorr : τ*(N : ℝ) ≤ ‖finiteComplexLagCorrelation f N h‖) :
    τ*(N : ℝ) ≤ (N-h : ℕ) :=
  hcorr.trans (finite_complex_lag_correlation_norm_bound f N h hf)

/-- The actual truncated correlation normalizes by its actual positive
remaining length, with no replacement by a full-length phase sum. -/
theorem finite_complex_large_lag_remaining_mean (f : ℕ → ℂ) (N h : ℕ)
    (hf : ∀ n < N, ‖f n‖ ≤ 1) (hN : 0 < N) (τ : ℝ) (hτ : 0 < τ)
    (hcorr : τ*(N : ℝ) ≤ ‖finiteComplexLagCorrelation f N h‖) :
    0 < N-h ∧ τ*(N : ℝ) ≤ (N-h : ℕ) ∧
      τ ≤ ‖finiteComplexSetMean (Finset.range (N-h)) (fun n => f (n+h)*star (f n))‖ := by
  have hlen := finite_complex_large_lag_remaining_length f N h hf τ hcorr
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hremr : (0 : ℝ) < (N-h : ℕ) := lt_of_lt_of_le (mul_pos hτ hNr) hlen
  have hrem : 0 < N-h := by exact_mod_cast hremr
  refine ⟨hrem, hlen, ?_⟩
  rw [finiteComplexSetMean, norm_div, Complex.norm_natCast, Finset.card_range]
  apply (le_div_iff₀ hremr).mpr
  have hle : (N-h : ℕ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N h
  exact (mul_le_mul_of_nonneg_left hle hτ.le).trans hcorr

end Hindman168
