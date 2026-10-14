import Hindman168.ScalarMvObservableInverse
import Hindman168.UnitCircleDenseSmallValues

namespace Hindman168
open MeasureTheory
open scoped BigOperators Classical Topology

/-- Actual dense values on an arbitrary nonempty finite orbit give actual
fixed-bump Haar discrepancy, uniformly over the original tolerance. -/
theorem unit_circle_finite_small_values_discrepancy {α : Type*} (s : Finset α)
    (hs : s.Nonempty) (f : α → UnitAddCircle) (δ ε : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : ε ≤ δ/10)
    (hdense : δ*(s.card : ℝ) ≤ (s.filter (fun a => ‖f a‖ ≤ ε)).card) :
    δ^2/40 ≤ ‖unitCircleFiniteDiscrepancy s f (unitCircleNormBumpObservable (δ/4))‖ := by
  have hm := unit_circle_dense_bump_mean s hs f (δ/4) ε δ (by linarith only [hδ, hε]) hdense
  have hi := unit_circle_norm_bump_haar_bound (δ/4) (by positivity) (by linarith only [hδ1])
  change δ^2/40 ≤ ‖finiteComplexSetMean s (fun a => unitCircleNormBumpObservable (δ/4) (f a))-
    ∫ t, unitCircleNormBumpObservable (δ/4) t ∂AddCircle.haarAddCircle‖
  rw [unit_circle_bump_complex_mean]
  change δ^2/40 ≤ ‖((_ : ℝ) : ℂ)-∫ t, (unitCircleNormBump (δ/4) t : ℂ) ∂AddCircle.haarAddCircle‖
  have hreal : (∫ t, (unitCircleNormBump (δ/4) t : ℂ) ∂AddCircle.haarAddCircle) =
      ((∫ t, unitCircleNormBump (δ/4) t ∂AddCircle.haarAddCircle : ℝ) : ℂ) := integral_ofReal
  rw [hreal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have he : δ*(δ/4-δ/10) ≤ δ*(δ/4-ε) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hε _) hδ.le
  exact (by nlinarith only [hm, hi, he, sq_nonneg δ] : δ^2/40 ≤
    (∑ a ∈ s, unitCircleNormBump (δ/4) (f a))/(s.card : ℝ)-
      ∫ t, unitCircleNormBump (δ/4) t ∂AddCircle.haarAddCircle).trans (le_abs_self _)

/-- Coarse nonconstant small-value degree step, using actual finite bump
discrepancy and the proved actual arbitrary-observable degree step. -/
theorem scalar_mv_small_values_coarse_degree_step (n D : ℕ)
    (hsmall : ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
      ∃ B : ℕ, 0 < B ∧ ScalarMvSmallValueEstimate (Fin n) D μ B)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ D+1 →
      ∀ N : ℕ, 0 < N → ∀ ε : ℝ, ε ≤ δ/10 →
        δ*((scalarMvIntegerCube (Fin n) N).card : ℝ) ≤
          ((scalarMvIntegerCube (Fin n) N).filter (fun x => ‖scalarMvCircleOrbit p x‖ ≤ ε)).card →
        ∃ q : ℕ, 0 < q ∧ q ≤ A ∧ ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨A, hA, hinv⟩ := scalar_mv_observable_degree_step n D hsmall (δ^2/40) (by positivity)
  refine ⟨A, hA, ?_⟩
  intro p hp N hN ε hε hdense
  exact hinv p hp N hN (unitCircleNormBumpObservable (δ/4))
    (unit_circle_norm_bump_observable_admissible (δ/4) (by positivity) (by linarith only [hδ1]))
    (unit_circle_finite_small_values_discrepancy (scalarMvIntegerCube (Fin n) N)
      (scalar_mv_integer_cube_nonempty (Fin n) N hN) (scalarMvCircleOrbit p) δ ε hδ hδ1 hε hdense)

theorem scalar_mv_linear_small_values_coarse_inverse (n : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ 1 →
      ∀ N : ℕ, 0 < N → ∀ ε : ℝ, ε ≤ δ/10 →
        δ*((scalarMvIntegerCube (Fin n) N).card : ℝ) ≤
          ((scalarMvIntegerCube (Fin n) N).filter (fun x => ‖scalarMvCircleOrbit p x‖ ≤ ε)).card →
        ∃ q : ℕ, 0 < q ∧ q ≤ A ∧ ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  exact scalar_mv_small_values_coarse_degree_step n 0
    (fun μ hμ _ => ⟨1, by omega, scalar_mv_small_value_estimate_zero (Fin n) μ hμ⟩) δ hδ hδ1

end Hindman168
