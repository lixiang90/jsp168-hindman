import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Module.Rat

/-! Finite vector polynomials are represented by actual finite lists of
degree/coefficient pairs. The representation need not be unique. All
operations below are finite and their actual real evaluations are proved,
so rational coefficient membership will not rely on topological closure. -/

namespace Hindman168

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]

noncomputable def finiteVectorPolynomialEval (p : List (ℕ × E)) (t : ℝ) : E :=
  (p.map (fun a => t ^ a.1 • a.2)).sum

noncomputable def finiteVectorPolynomialScale (r : ℚ) (p : List (ℕ × E)) : List (ℕ × E) :=
  p.map (fun a => (a.1, r • a.2))

omit [Module ℚ E] in
 theorem finiteVectorPolynomialEval_nil (t : ℝ) :
    finiteVectorPolynomialEval ([] : List (ℕ × E)) t = 0 := rfl

omit [Module ℚ E] in
 theorem finiteVectorPolynomialEval_cons (a : ℕ × E) (p : List (ℕ × E)) (t : ℝ) :
    finiteVectorPolynomialEval (a :: p) t = t ^ a.1 • a.2 + finiteVectorPolynomialEval p t := rfl

omit [Module ℚ E] in
 theorem finiteVectorPolynomialEval_append (p q : List (ℕ × E)) (t : ℝ) :
    finiteVectorPolynomialEval (p ++ q) t =
      finiteVectorPolynomialEval p t + finiteVectorPolynomialEval q t := by
  simp only [finiteVectorPolynomialEval, List.map_append, List.sum_append]

omit [Module ℚ E] in
 theorem finiteVectorPolynomialEval_singleton (n : ℕ) (v : E) (t : ℝ) :
    finiteVectorPolynomialEval [(n, v)] t = t ^ n • v := by
  simp only [finiteVectorPolynomialEval_cons, finiteVectorPolynomialEval_nil, add_zero]

 theorem finiteVectorPolynomialEval_scale (r : ℚ) (p : List (ℕ × E)) (t : ℝ) :
    finiteVectorPolynomialEval (finiteVectorPolynomialScale r p) t =
      r • finiteVectorPolynomialEval p t := by
  induction p with
  | nil => simp only [finiteVectorPolynomialScale, List.map_nil, finiteVectorPolynomialEval_nil, smul_zero]
  | cons a p ih =>
    simp only [finiteVectorPolynomialScale, List.map_cons, finiteVectorPolynomialEval_cons,
      smul_add, smul_comm (t ^ a.1) r a.2]
    exact congrArg (fun z => (r • (t ^ a.1 • a.2)) + z) ih

omit [Module ℚ E] in
 theorem finiteVectorPolynomialEval_continuous (p : List (ℕ × E)) :
    Continuous (finiteVectorPolynomialEval p) := by
  induction p with
  | nil => exact continuous_const
  | cons a p ih =>
    exact ((continuous_id.pow a.1).smul continuous_const).add ih

end Hindman168
