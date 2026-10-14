import Hindman168.FiniteVectorPolynomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual Bochner primitives of finite vector polynomials have finite
coefficient lists. Each coefficient is divided by its new positive degree
in Q. This gives exact rational endpoints without closed-subspace assumptions. -/

namespace Hindman168
open MeasureTheory
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]

noncomputable def finiteVectorPolynomialPrimitive (p : List (ℕ × E)) : List (ℕ × E) :=
  p.map (fun a => (a.1 + 1, ((a.1 + 1 : ℚ)⁻¹) • a.2))

variable [CompleteSpace E]

 theorem finiteVectorPolynomial_monomial_integral (n : ℕ) (v : E) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, s ^ n • v) = t ^ (n + 1) • ((n + 1 : ℚ)⁻¹ • v) := by
  rw [intervalIntegral.integral_smul_const, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, div_eq_mul_inv, mul_smul]
  have hc : (((n + 1 : ℚ)⁻¹ : ℚ) : ℝ) = (n + 1 : ℝ)⁻¹ := by push_cast; rfl
  rw [← hc, Rat.cast_smul_eq_qsmul]

 theorem finiteVectorPolynomialEval_primitive (p : List (ℕ × E)) (t : ℝ) :
    finiteVectorPolynomialEval (finiteVectorPolynomialPrimitive p) t =
      ∫ s in (0 : ℝ)..t, finiteVectorPolynomialEval p s := by
  induction p with
  | nil => simp only [finiteVectorPolynomialPrimitive, List.map_nil,
      finiteVectorPolynomialEval_nil, intervalIntegral.integral_zero]
  | cons a p ih =>
    change t ^ (a.1 + 1) • ((a.1 + 1 : ℚ)⁻¹ • a.2) +
      finiteVectorPolynomialEval (finiteVectorPolynomialPrimitive p) t =
        ∫ s in (0 : ℝ)..t, s ^ a.1 • a.2 + finiteVectorPolynomialEval p s
    have hf : IntervalIntegrable (fun s : ℝ => s ^ a.1 • a.2) volume 0 t :=
      ((continuous_id.pow a.1).smul continuous_const).intervalIntegrable 0 t
    have hg : IntervalIntegrable (finiteVectorPolynomialEval p) volume 0 t :=
      (finiteVectorPolynomialEval_continuous p).intervalIntegrable 0 t
    rw [intervalIntegral.integral_add hf hg, finiteVectorPolynomial_monomial_integral, ih]

end Hindman168
