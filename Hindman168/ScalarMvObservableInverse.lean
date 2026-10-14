import Hindman168.UnitCircleFiniteObservablePhaseSelection
import Hindman168.ScalarMvPhaseDegreeStep
import Hindman168.UnitCirclePolynomialInverse

namespace Hindman168
open scoped BigOperators Classical Topology

noncomputable def scalarMvCircleOrbit {κ : Type*}
    (p : MvPolynomial κ ℝ) (x : κ → ℤ) : UnitAddCircle :=
  ((MvPolynomial.eval (fun j => (x j : ℝ)) p : ℝ) : UnitAddCircle)

theorem scalar_mv_fourier_phase {κ : Type*}
    (p : MvPolynomial κ ℝ) (x : κ → ℤ) (k : ℤ) :
    fourier k (scalarMvCircleOrbit p x) = scalarMvPolynomialPhase (MvPolynomial.C (k : ℝ)*p) x := by
  rw [scalarMvCircleOrbit, fourier_apply, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  simp only [scalarMvPolynomialPhase, map_mul, MvPolynomial.eval_C]

/-- Actual arbitrary-observable inverse from the phase degree theorem.
The Fourier frequency is genuinely selected from one fixed compact family. -/
theorem scalar_mv_observable_inverse_from_phase (n D : ℕ)
    (hphase : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ A : ℕ, 0 < A ∧
      ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ D → ∀ N : ℕ, 0 < N →
        η ≤ ‖finiteComplexSetMean (scalarMvIntegerCube (Fin n) N) (scalarMvPolynomialPhase p)‖ →
        ∃ q : ℕ, 0 < q ∧ q ≤ A ∧ ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℕ, 0 < B ∧ ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ D →
      ∀ N : ℕ, 0 < N → ∀ F ∈ unitLipschitzObservables UnitAddCircle,
        δ ≤ ‖unitCircleFiniteDiscrepancy (scalarMvIntegerCube (Fin n) N) (scalarMvCircleOrbit p) F‖ →
        ∃ Q : ℕ, 0 < Q ∧ Q ≤ B ∧ ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖(((Q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ) := by
  obtain ⟨η, hη, hη1, K, hK, hmode⟩ := unit_circle_finite_observable_phase_selection δ hδ
  obtain ⟨A, hA, hinv⟩ := hphase η hη hη1
  let B := A*K+1
  have hB : 0 < B := by dsimp only [B]; omega
  have hAB : A ≤ B := (Nat.le_mul_of_pos_right A hK).trans (by dsimp only [B]; omega)
  refine ⟨B, hB, ?_⟩
  intro p hp N hN F hF hbad
  obtain ⟨k, hk0, hkK, hkmean⟩ := hmode (scalarMvIntegerCube (Fin n) N)
    (scalar_mv_integer_cube_nonempty (Fin n) N hN) (scalarMvCircleOrbit p) F hF hbad
  have hscaled : (MvPolynomial.C (k : ℝ)*p).totalDegree ≤ D := by
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa only [MvPolynomial.totalDegree_C, zero_add] using hp)
  have he : (fun x => fourier k (scalarMvCircleOrbit p x)) =
      scalarMvPolynomialPhase (MvPolynomial.C (k : ℝ)*p) :=
    funext (fun x => scalar_mv_fourier_phase p x k)
  rw [he] at hkmean
  obtain ⟨q, hq, hqA, hcoeff⟩ := hinv (MvPolynomial.C (k : ℝ)*p) hscaled N hN hkmean
  let Q := q*k.natAbs
  have hQ : 0 < Q := Nat.mul_pos hq (Int.natAbs_pos.mpr hk0)
  have hQB : Q ≤ B := (Nat.mul_le_mul hqA hkK).trans (by dsimp only [B]; omega)
  refine ⟨Q, hQ, hQB, ?_⟩
  intro I hI
  have hb := hcoeff I hI
  rw [MvPolynomial.coeff_C_mul] at hb
  have hqeq : (Q : ℝ)*MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p =
      (k.natAbs : ℝ)*((q : ℝ)*MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p) := by
    dsimp only [Q]
    push_cast
    ring
  rw [hqeq, unit_circle_nat_abs_multiplier_norm]
  have heq : (k : ℝ)*((q : ℝ)*MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p) =
      (q : ℝ)*((k : ℝ)*MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p) := by ring
  rw [heq]
  exact hb.trans (by exact_mod_cast hAB)

theorem scalar_mv_observable_degree_step (n D : ℕ)
    (hsmall : ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
      ∃ A : ℕ, 0 < A ∧ ScalarMvSmallValueEstimate (Fin n) D μ A)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℕ, 0 < B ∧ ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ D+1 →
      ∀ N : ℕ, 0 < N → ∀ F ∈ unitLipschitzObservables UnitAddCircle,
        δ ≤ ‖unitCircleFiniteDiscrepancy (scalarMvIntegerCube (Fin n) N) (scalarMvCircleOrbit p) F‖ →
        ∃ Q : ℕ, 0 < Q ∧ Q ≤ B ∧ ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖(((Q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ) := by
  exact scalar_mv_observable_inverse_from_phase n (D+1)
    (fun η hη hη1 => scalar_mv_phase_degree_step n D hsmall η hη hη1) δ hδ

theorem scalar_mv_linear_observable_inverse (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℕ, 0 < B ∧ ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ 1 →
      ∀ N : ℕ, 0 < N → ∀ F ∈ unitLipschitzObservables UnitAddCircle,
        δ ≤ ‖unitCircleFiniteDiscrepancy (scalarMvIntegerCube (Fin n) N) (scalarMvCircleOrbit p) F‖ →
        ∃ Q : ℕ, 0 < Q ∧ Q ≤ B ∧ ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
          (N : ℝ)^(∑ j, I j)*‖(((Q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ) := by
  exact scalar_mv_observable_inverse_from_phase n 1
    (fun η hη hη1 => scalar_mv_linear_phase_inverse n η hη hη1) δ hδ

end Hindman168
