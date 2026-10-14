import Hindman168.ScalarPolynomialDifference
import Hindman168.FinitePositiveLagDensity
import Hindman168.UnitCirclePhaseDistance

namespace Hindman168
open Polynomial
open scoped BigOperators Classical

noncomputable def scalarPolynomialPhase (p : ℝ[X]) (n : ℕ) : ℂ :=
  (AddCircle.toCircle ((p.eval (n : ℝ) : ℝ) : UnitAddCircle) : ℂ)

theorem scalar_polynomial_phase_norm (p : ℝ[X]) (n : ℕ) : ‖scalarPolynomialPhase p n‖ = 1 :=
  Circle.norm_coe _

theorem unit_circle_phase_sub (u v : ℝ) :
    (AddCircle.toCircle (u : UnitAddCircle) : ℂ)*star (AddCircle.toCircle (v : UnitAddCircle) : ℂ) =
      (AddCircle.toCircle ((u-v : ℝ) : UnitAddCircle) : ℂ) := by
  rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul,
    ← AddCircle.toCircle_neg, ← AddCircle.toCircle_add,
    ← AddCircle.coe_neg, ← AddCircle.coe_add]
  simp only [sub_eq_add_neg]

theorem scalar_polynomial_phase_difference (p : ℝ[X]) (h n : ℕ) :
    scalarPolynomialPhase p (n+h)*star (scalarPolynomialPhase p n) =
      scalarPolynomialPhase (scalarPolynomialDifference p (h : ℝ)) n := by
  rw [scalarPolynomialPhase, scalarPolynomialPhase, unit_circle_phase_sub,
    scalarPolynomialPhase, scalar_polynomial_difference_eval, Nat.cast_add]

theorem scalar_polynomial_lag_correlation (p : ℝ[X]) (N h : ℕ) :
    finiteComplexLagCorrelation (scalarPolynomialPhase p) N h =
      ∑ n ∈ Finset.range (N-h), scalarPolynomialPhase (scalarPolynomialDifference p (h : ℝ)) n := by
  simp only [finiteComplexLagCorrelation, scalar_polynomial_phase_difference]

/-- Actual dense positive shifts, actual remaining intervals, and actual
large means of the genuine lower-degree polynomial phases. -/
theorem scalar_polynomial_dense_difference_means (p : ℝ[X]) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hlarge : 4 ≤ δ^2*(N : ℝ))
    (hmean : δ ≤ ‖finiteComplexSetMean (Finset.range N) (scalarPolynomialPhase p)‖) :
    ∃ T : Finset ℕ, δ^2/8*(N : ℝ) ≤ T.card ∧
      ∀ h ∈ T, 0 < h ∧ h < N ∧ 0 < N-h ∧ δ^2/8*(N : ℝ) ≤ (N-h : ℕ) ∧
        δ^2/8 ≤ ‖finiteComplexSetMean (Finset.range (N-h))
          (scalarPolynomialPhase (scalarPolynomialDifference p (h : ℝ)))‖ := by
  let T := (positiveNaturalLags N).filter (fun h => δ^2/8*(N : ℝ) ≤
    ‖finiteComplexLagCorrelation (scalarPolynomialPhase p) N h‖)
  have hf : ∀ n < N, ‖scalarPolynomialPhase p n‖ ≤ 1 :=
    fun n _ => (scalar_polynomial_phase_norm p n).le
  refine ⟨T, finite_complex_positive_lag_density _ N hN hf δ hδ hlarge hmean, ?_⟩
  intro h hh
  have hmem := Finset.mem_filter.mp hh
  have hpos := (positive_natural_lags_mem N h).mp hmem.1
  obtain ⟨hrem, hlen, hcorr⟩ := finite_complex_large_lag_remaining_mean
    (scalarPolynomialPhase p) N h hf hN (δ^2/8) (by positivity) hmem.2
  refine ⟨hpos.2, hpos.1, hrem, hlen, ?_⟩
  simpa only [scalar_polynomial_phase_difference] using hcorr

end Hindman168
