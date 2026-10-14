import Hindman168.FiniteVectorPolynomialDegree
import Mathlib.Algebra.MvPolynomial.Degrees

namespace Hindman168

variable {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def vectorPolynomialMultivariateProjection
    (ell : E →ₗ[ℝ] ℝ) (P : MvPolynomial σ ℝ) : List (ℕ × E) → MvPolynomial σ ℝ
  | [] => 0
  | a :: p => MvPolynomial.C (ell a.2) * P ^ a.1 + vectorPolynomialMultivariateProjection ell P p

theorem vectorPolynomialMultivariateProjection_eval
    (ell : E →ₗ[ℝ] ℝ) (P : MvPolynomial σ ℝ) (p : List (ℕ × E)) (z : σ → ℝ) :
    MvPolynomial.eval z (vectorPolynomialMultivariateProjection ell P p) =
      ell (finiteVectorPolynomialEval p (MvPolynomial.eval z P)) := by
  induction p with
  | nil => simp only [vectorPolynomialMultivariateProjection, map_zero, finiteVectorPolynomialEval_nil]
  | cons a p ih =>
    simp only [vectorPolynomialMultivariateProjection, map_add, map_mul, map_pow,
      MvPolynomial.eval_C, ih, finiteVectorPolynomialEval_cons, map_smul, smul_eq_mul]
    ring

theorem vectorPolynomialMultivariateProjection_degree
    (ell : E →ₗ[ℝ] ℝ) (P : MvPolynomial σ ℝ) (p : List (ℕ × E)) (d : ℕ)
    (hp : finiteVectorPolynomialDegreeLE p d) :
    (vectorPolynomialMultivariateProjection ell P p).totalDegree ≤ d * P.totalDegree := by
  induction p with
  | nil => simp only [vectorPolynomialMultivariateProjection, MvPolynomial.totalDegree_zero, Nat.zero_le]
  | cons a p ih =>
    have ha := hp a (List.mem_cons_self)
    have ht : finiteVectorPolynomialDegreeLE p d := fun b hb => hp b (List.mem_cons_of_mem _ hb)
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le _ (ih ht)
    apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_C, zero_add]
    apply (MvPolynomial.totalDegree_pow _ _).trans
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right P.totalDegree ha

end Hindman168
