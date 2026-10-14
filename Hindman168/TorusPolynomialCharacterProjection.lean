import Hindman168.UnitTorusFiniteObservablePhaseSelection
import Hindman168.ScalarMvPolynomialInverse

namespace Hindman168
open scoped BigOperators Classical

noncomputable def torusPolynomialCharacterProjection {κ σ : Type*} [Fintype κ]
    (p : κ → MvPolynomial σ ℝ) (k : κ → ℤ) : MvPolynomial σ ℝ :=
  ∑ j, MvPolynomial.C (k j : ℝ)*p j

noncomputable def torusMvPolynomialOrbit {κ σ : Type*} [Fintype κ]
    (p : κ → MvPolynomial σ ℝ) (x : σ → ℤ) : UnitAddTorus κ :=
  fun j => ((MvPolynomial.eval (fun i => (x i : ℝ)) (p j) : ℝ) : UnitAddCircle)

theorem torus_polynomial_character_projection_degree {κ σ : Type*} [Fintype κ]
    (p : κ → MvPolynomial σ ℝ) (k : κ → ℤ) (D : ℕ) (hp : ∀ j, (p j).totalDegree ≤ D) :
    (torusPolynomialCharacterProjection p k).totalDegree ≤ D := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa only [MvPolynomial.totalDegree_C, zero_add] using hp j)

theorem torus_polynomial_character_projection_coefficient {κ σ : Type*} [Fintype κ]
    (p : κ → MvPolynomial σ ℝ) (k : κ → ℤ) (I : σ →₀ ℕ) :
    MvPolynomial.coeff I (torusPolynomialCharacterProjection p k) =
      ∑ j, (k j : ℝ)*MvPolynomial.coeff I (p j) := by
  simp only [torusPolynomialCharacterProjection, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]

theorem torus_polynomial_character_projection_eval {κ σ : Type*} [Fintype κ]
    (p : κ → MvPolynomial σ ℝ) (k : κ → ℤ) (x : σ → ℝ) :
    MvPolynomial.eval x (torusPolynomialCharacterProjection p k) =
      ∑ j, (k j : ℝ)*MvPolynomial.eval x (p j) := by
  simp only [torusPolynomialCharacterProjection, map_sum, map_mul, MvPolynomial.eval_C]

theorem circle_phase_real_sum {α : Type*} (s : Finset α) (v : α → ℝ) :
    (AddCircle.toCircle ((∑ a ∈ s, v a : ℝ) : UnitAddCircle) : ℂ) =
      ∏ a ∈ s, (AddCircle.toCircle ((v a : ℝ) : UnitAddCircle) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddCircle.coe_add,
      AddCircle.toCircle_add, Circle.coe_mul, ih]

/-- The actual multidimensional Fourier mode equals the phase of the
ACTUAL original integer character projection on every original sample. -/
theorem torus_mv_fourier_character_phase {κ σ : Type*} [Fintype κ]
    (p : κ → MvPolynomial σ ℝ) (k : κ → ℤ) (x : σ → ℤ) :
    UnitAddTorus.mFourier k (torusMvPolynomialOrbit p x) =
      scalarMvPolynomialPhase (torusPolynomialCharacterProjection p k) x := by
  rw [scalarMvPolynomialPhase, torus_polynomial_character_projection_eval, circle_phase_real_sum]
  change (∏ j, fourier (k j) (((MvPolynomial.eval (fun i => (x i : ℝ)) (p j) : ℝ) : UnitAddCircle))) = _
  simp_rw [fourier_apply, ← AddCircle.coe_zsmul, zsmul_eq_mul]

theorem torus_integer_character_scale_nonzero {κ : Type*}
    (k : κ → ℤ) (hk : k ≠ 0) (q : ℕ) (hq : 0 < q) :
    (fun j => (q : ℤ)*k j) ≠ 0 := by
  intro h
  apply hk
  funext j
  have hj : (q : ℤ)*k j = 0 := congrFun h j
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  exact (mul_eq_zero.mp hj).resolve_left hqz

theorem torus_integer_character_scale_size {κ : Type*} [Fintype κ]
    (k : κ → ℤ) (q : ℕ) :
    (∑ j, ((q : ℤ)*k j).natAbs) = q*(∑ j, (k j).natAbs) := by
  simp only [Int.natAbs_mul, Int.natAbs_natCast, Finset.mul_sum]

theorem torus_integer_character_scale_coefficient {κ σ : Type*} [Fintype κ]
    (p : κ → MvPolynomial σ ℝ) (k : κ → ℤ) (q : ℕ) (I : σ →₀ ℕ) :
    (∑ j, (((q : ℤ)*k j : ℤ) : ℝ)*MvPolynomial.coeff I (p j)) =
      (q : ℝ)*MvPolynomial.coeff I (torusPolynomialCharacterProjection p k) := by
  rw [torus_polynomial_character_projection_coefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

end Hindman168
