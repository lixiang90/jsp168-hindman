import Hindman168.ScalarMvSmallValuesZero

namespace Hindman168
open scoped BigOperators Classical Topology

/-- COMPLETE actual scalar multiparameter small-value inverse for EVERY
degree and fixed input dimension, including the ORIGINAL constant and
epsilon=0. Natural degree induction discharges every former IH. -/
theorem scalar_mv_polynomial_small_values_inverse (n D : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ B : ℕ, 0 < B ∧ ScalarMvSmallValueEstimate (Fin n) D δ B := by
  induction D generalizing δ with
  | zero => exact ⟨1, by omega, scalar_mv_small_value_estimate_zero (Fin n) δ hδ⟩
  | succ D ih =>
    obtain ⟨B, hB, hcoarse⟩ := scalar_mv_small_values_coarse_degree_step n D
      (fun μ hμ hμ1 => ih μ hμ hμ1) δ hδ hδ1
    exact scalar_mv_small_value_estimate_from_coarse n (D+1) B hB δ hδ hcoarse

/-- COMPLETE actual scalar polynomial phase inverse on equal cubes for
EVERY degree and EVERY positive original length. One fixed bound precedes
all real polynomial coefficients and N; one multiplier controls every
original positive-weight coefficient. No analytic inverse is assumed. -/
theorem scalar_mv_polynomial_phase_inverse (n D : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ D →
      ∀ N : ℕ, 0 < N → δ ≤ ‖finiteComplexSetMean (scalarMvIntegerCube (Fin n) N)
        (scalarMvPolynomialPhase p)‖ →
        ∃ q : ℕ, 0 < q ∧ q ≤ A ∧ ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  cases D with
  | zero =>
    refine ⟨1, by omega, ?_⟩
    intro p hp N _ _
    refine ⟨1, by omega, le_rfl, ?_⟩
    intro I hI
    simp only [scalar_mv_coefficient_zero_above_degree p 0 hp I hI,
      mul_zero, AddCircle.coe_zero, norm_zero, Nat.cast_one]
    norm_num
  | succ D =>
    exact scalar_mv_phase_degree_step n D
      (fun μ hμ hμ1 => scalar_mv_polynomial_small_values_inverse n D μ hμ hμ1) δ hδ hδ1

/-- COMPLETE actual scalar multiparameter inverse for arbitrary bounded
unit Lipschitz circle observables, on EVERY positive original length. -/
theorem scalar_mv_polynomial_observable_inverse (n D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℕ, 0 < A ∧ ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ D →
      ∀ N : ℕ, 0 < N → ∀ F ∈ unitLipschitzObservables UnitAddCircle,
        δ ≤ ‖unitCircleFiniteDiscrepancy (scalarMvIntegerCube (Fin n) N) (scalarMvCircleOrbit p) F‖ →
        ∃ q : ℕ, 0 < q ∧ q ≤ A ∧ ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  exact scalar_mv_observable_inverse_from_phase n D
    (fun η hη hη1 => scalar_mv_polynomial_phase_inverse n D η hη hη1) δ hδ

theorem scalar_mv_polynomial_small_values_coarse_inverse (n D : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ D →
      ∀ N : ℕ, 0 < N → ∀ ε : ℝ, ε ≤ δ/10 →
        δ*((scalarMvIntegerCube (Fin n) N).card : ℝ) ≤
          ((scalarMvIntegerCube (Fin n) N).filter (fun x => ‖scalarMvCircleOrbit p x‖ ≤ ε)).card →
        ∃ q : ℕ, 0 < q ∧ q ≤ A ∧ ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨A, hA, hinv⟩ := scalar_mv_polynomial_observable_inverse n D (δ^2/40) (by positivity)
  refine ⟨A, hA, ?_⟩
  intro p hp N hN ε hε hdense
  exact hinv p hp N hN (unitCircleNormBumpObservable (δ/4))
    (unit_circle_norm_bump_observable_admissible (δ/4) (by positivity) (by linarith only [hδ1]))
    (unit_circle_finite_small_values_discrepancy (scalarMvIntegerCube (Fin n) N)
      (scalar_mv_integer_cube_nonempty (Fin n) N hN) (scalarMvCircleOrbit p) δ ε hδ hδ1 hε hdense)

end Hindman168
