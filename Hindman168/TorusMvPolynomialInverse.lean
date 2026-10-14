import Hindman168.TorusPolynomialCharacterProjection

namespace Hindman168
open scoped BigOperators Classical Topology

/-- COMPLETE actual polynomial inverse for an arbitrary fixed-dimensional
TARGET torus, on equal cubes of arbitrary fixed INPUT dimension and degree.
One bound precedes every real coefficient,N and arbitrary unit Lipschitz
observable. The nonzero integer character is ACTUALLY produced, and controls
EVERY original positive-weight coefficient with the SAME character. -/
theorem torus_mv_polynomial_observable_inverse (m n D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℕ, 0 < A ∧ ∀ p : Fin m → MvPolynomial (Fin n) ℝ,
      (∀ j, (p j).totalDegree ≤ D) → ∀ N : ℕ, 0 < N →
        ∀ F ∈ unitLipschitzObservables (UnitAddTorus (Fin m)),
          δ ≤ ‖unitTorusFiniteDiscrepancy (scalarMvIntegerCube (Fin n) N)
            (torusMvPolynomialOrbit p) F‖ →
          ∃ v : Fin m → ℤ, v ≠ 0 ∧ (∑ j, (v j).natAbs) ≤ A ∧
            ∀ I : Fin n → ℕ, 0 < (∑ i, I i) →
              (N : ℝ)^(∑ i, I i)*‖((∑ j, (v j : ℝ)*MvPolynomial.coeff
                (Finsupp.equivFunOnFinite.symm I) (p j) : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨η, hη, hη1, K, hK, hmode⟩ := unit_torus_finite_observable_phase_selection (Fin m) δ hδ
  obtain ⟨A₀, hA₀, hinv⟩ := scalar_mv_polynomial_phase_inverse n D η hη hη1
  let A := A₀*K+1
  have hA : 0 < A := by dsimp only [A]; omega
  have hA₀A : A₀ ≤ A := (Nat.le_mul_of_pos_right A₀ hK).trans (by dsimp only [A]; omega)
  refine ⟨A, hA, ?_⟩
  intro p hp N hN F hF hbad
  obtain ⟨k, hk, hkK, hkmean⟩ := hmode (scalarMvIntegerCube (Fin n) N)
    (scalar_mv_integer_cube_nonempty (Fin n) N hN) (torusMvPolynomialOrbit p) F hF hbad
  have he : (fun x => UnitAddTorus.mFourier k (torusMvPolynomialOrbit p x)) =
      scalarMvPolynomialPhase (torusPolynomialCharacterProjection p k) :=
    funext (fun x => torus_mv_fourier_character_phase p k x)
  rw [he] at hkmean
  obtain ⟨q, hq, hqA₀, hcoeff⟩ := hinv (torusPolynomialCharacterProjection p k)
    (torus_polynomial_character_projection_degree p k D hp) N hN hkmean
  let v := fun j => (q : ℤ)*k j
  have hv : v ≠ 0 := torus_integer_character_scale_nonzero k hk q hq
  have hvA : (∑ j, (v j).natAbs) ≤ A := by
    rw [show (∑ j, (v j).natAbs) = q*(∑ j, (k j).natAbs) from
      torus_integer_character_scale_size k q]
    exact (Nat.mul_le_mul hqA₀ hkK).trans (by dsimp only [A]; omega)
  refine ⟨v, hv, hvA, ?_⟩
  intro I hI
  have heq := torus_integer_character_scale_coefficient p k q (Finsupp.equivFunOnFinite.symm I)
  change (∑ j, (v j : ℝ)*MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) (p j)) = _ at heq
  rw [heq]
  exact (hcoeff I hI).trans (by exact_mod_cast hA₀A)

end Hindman168
