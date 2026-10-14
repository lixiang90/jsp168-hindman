import Hindman168.ScalarPolynomialPhaseLags
import Hindman168.UnitCircleGeometricMean

namespace Hindman168
open Polynomial
open scoped BigOperators Classical

theorem scalar_polynomial_linear_phase_value (p : ℝ[X]) (hp : p.natDegree ≤ 1) (n : ℕ) :
    scalarPolynomialPhase p n =
      (AddCircle.toCircle ((p.coeff 0 : ℝ) : UnitAddCircle) : ℂ)*
        (AddCircle.toCircle (((n : ℝ)*p.coeff 1 : ℝ) : UnitAddCircle) : ℂ) := by
  have he : p.eval (n : ℝ) = p.coeff 0+(n : ℝ)*p.coeff 1 := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hp]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    ring
  rw [scalarPolynomialPhase, he, AddCircle.coe_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem scalar_polynomial_linear_phase_mean_norm (p : ℝ[X]) (hp : p.natDegree ≤ 1) (N : ℕ) :
    ‖finiteComplexSetMean (Finset.range N) (scalarPolynomialPhase p)‖ =
      ‖finiteComplexSetMean (Finset.range N) (fun n =>
        (AddCircle.toCircle (((n : ℝ)*p.coeff 1 : ℝ) : UnitAddCircle) : ℂ))‖ := by
  have he : finiteComplexSetMean (Finset.range N) (scalarPolynomialPhase p) =
      (AddCircle.toCircle ((p.coeff 0 : ℝ) : UnitAddCircle) : ℂ)*
        finiteComplexSetMean (Finset.range N) (fun n =>
          (AddCircle.toCircle (((n : ℝ)*p.coeff 1 : ℝ) : UnitAddCircle) : ℂ)) := by
    simp only [finiteComplexSetMean, scalar_polynomial_linear_phase_value p hp,
      ← Finset.mul_sum, mul_div_assoc]
  rw [he, norm_mul, Circle.norm_coe, one_mul]

theorem scalar_polynomial_linear_phase_inverse (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℕ, 0 < A ∧ ∀ p : ℝ[X], p.natDegree ≤ 1 → ∀ N : ℕ, 0 < N →
      δ ≤ ‖finiteComplexSetMean (Finset.range N) (scalarPolynomialPhase p)‖ →
      ∃ q : ℕ, 0 < q ∧ q ≤ A ∧
        (N : ℝ)*‖(((q : ℝ)*p.coeff 1 : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  let A := ⌈1/(2*δ)⌉₊+1
  refine ⟨A, by dsimp only [A]; omega, ?_⟩
  intro p hp N hN hmean
  rw [scalar_polynomial_linear_phase_mean_norm p hp N] at hmean
  have hn := unit_circle_large_linear_mean_inverse (p.coeff 1) N hN δ hδ hmean
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have he : (N : ℝ)*(1/(2*δ*(N : ℝ))) = 1/(2*δ) := by field_simp
  have hb : (N : ℝ)*‖((p.coeff 1 : ℝ) : UnitAddCircle)‖ ≤ 1/(2*δ) := by
    simpa only [he] using mul_le_mul_of_nonneg_left hn hNr.le
  have hA : 1/(2*δ) ≤ (A : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈1/(2*δ)⌉₊ ≤ A by dsimp only [A]; omega))
  exact ⟨1, by omega, by dsimp only [A]; omega, by simpa only [Nat.cast_one, one_mul] using hb.trans hA⟩

end Hindman168
