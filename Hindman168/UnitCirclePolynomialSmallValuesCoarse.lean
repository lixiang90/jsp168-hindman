import Hindman168.UnitCirclePolynomialInverse
import Hindman168.UnitCircleDenseSmallValues

namespace Hindman168
open Polynomial MeasureTheory
open scoped BigOperators Classical Topology

theorem unit_circle_polynomial_small_values_discrepancy (p : ℝ[X]) (N : ℕ) (hN : 0 < N)
    (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : ε ≤ δ/10)
    (hdense : δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
      ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε)).card) :
    δ^2/40 ≤ ‖unitCirclePolynomialDiscrepancy p N (unitCircleNormBumpObservable (δ/4))‖ := by
  have hm := unit_circle_dense_bump_mean (Finset.range N) (Finset.nonempty_range_iff.mpr hN.ne')
    (fun n => ((p.eval (n : ℝ) : ℝ) : UnitAddCircle)) (δ/4) ε δ
    (by linarith) (by simpa using hdense)
  have hi := unit_circle_norm_bump_haar_bound (δ/4) (by positivity) (by linarith)
  rw [unit_circle_polynomial_discrepancy_apply, unit_circle_bump_complex_mean]
  change δ^2/40 ≤ ‖((_ : ℝ) : ℂ)-∫ t, (unitCircleNormBump (δ/4) t : ℂ) ∂AddCircle.haarAddCircle‖
  have hreal : (∫ t, (unitCircleNormBump (δ/4) t : ℂ) ∂AddCircle.haarAddCircle) =
      ((∫ t, unitCircleNormBump (δ/4) t ∂AddCircle.haarAddCircle : ℝ) : ℂ) := integral_ofReal
  rw [hreal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have he : δ*(δ/4-δ/10) ≤ δ*(δ/4-ε) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hε _) hδ.le
  exact (by nlinarith [hm, hi] : δ^2/40 ≤
    (∑ n ∈ Finset.range N, unitCircleNormBump (δ/4) ((p.eval (n : ℝ) : ℝ) : UnitAddCircle))/
      (↑(Finset.range N).card : ℝ)-∫ t, unitCircleNormBump (δ/4) t ∂AddCircle.haarAddCircle).trans
        (le_abs_self _)

/-- Actual dense small polynomial values yield a genuine simultaneous
coarse inverse, uniformly in the original tolerance epsilon. The constant
coefficient is not claimed controlled at this analytic coarse stage. -/
theorem unit_circle_polynomial_small_values_coarse_inverse (D : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ B : ℕ, 0 < B ∧ ∀ p : ℝ[X], p.natDegree ≤ D → ∀ N : ℕ, 0 < N → ∀ ε : ℝ,
      ε ≤ δ/10 →
      δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
        ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε)).card →
      ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ ∀ i : ℕ, 0 < i → i ≤ D →
        (N : ℝ)^i*‖(((q : ℝ)*p.coeff i : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ) := by
  obtain ⟨B, hB, hinv⟩ := unit_circle_polynomial_inverse D (δ^2/40) (by positivity)
  refine ⟨B, hB, ?_⟩
  intro p hp N hN ε hε hdense
  exact hinv p hp N hN (unitCircleNormBumpObservable (δ/4))
    (unit_circle_norm_bump_observable_admissible (δ/4) (by positivity) (by linarith))
    (unit_circle_polynomial_small_values_discrepancy p N hN δ ε hδ hδ1 hε hdense)

end Hindman168
