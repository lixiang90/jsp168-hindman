import Hindman168.FinitePositiveLagDensity

namespace Hindman168
open scoped Classical

/-- One unit sample has large mean and no positive nonzero zero-extended
correlation. Thus a positive-lag density theorem needs a large-N condition
(or a different scope including the zero lag). -/
theorem single_sample_positive_lag_counterexample :
    ‖finiteComplexSetMean (Finset.range 1) (fun _ : ℕ => (1 : ℂ))‖ > (1 : ℝ)/2 ∧
      ∀ h : ℕ, 0 < h → finiteComplexLagCorrelation (fun _ : ℕ => (1 : ℂ)) 1 h = 0 := by
  constructor
  · norm_num [finiteComplexSetMean]
  · intro h hh
    exact finite_complex_lag_correlation_zero_of_large_lag _ 1 h hh

/-- Actual failure of the unrestricted one-point positive-lag cardinality
conclusion, with the actual published [N] index convention at N=1. -/
theorem single_sample_positive_lag_density_failure :
    (((Finset.Icc 1 1).filter (fun h : ℕ => ((1 : ℝ)/2)^2/8 <
      ‖finiteComplexLagCorrelation (fun _ : ℕ => (1 : ℂ)) 1 h‖)).card : ℝ) <
        ((1 : ℝ)/2)^2/8 := by
  have hempty : (Finset.Icc 1 1).filter (fun h : ℕ => ((1 : ℝ)/2)^2/8 <
      ‖finiteComplexLagCorrelation (fun _ : ℕ => (1 : ℂ)) 1 h‖) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro h hh
    have hv := Finset.mem_filter.mp hh
    have h1 : h=1 := by have hb := Finset.mem_Icc.mp hv.1; omega
    subst h
    norm_num [finiteComplexLagCorrelation] at hv
  rw [hempty]
  norm_num

end Hindman168
