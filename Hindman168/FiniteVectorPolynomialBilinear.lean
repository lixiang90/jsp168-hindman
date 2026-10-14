import Hindman168.FiniteVectorPolynomial

/-! Actual bilinear evaluation of finite vector polynomials. Expanding
all pairs yields a finite representation with summed degrees and actual
bilinear coefficient values. No commutative ring structure on E is used. -/

namespace Hindman168

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def finiteVectorPolynomialBilinear
    (B : E →L[ℝ] (E →L[ℝ] E)) (p q : List (ℕ × E)) : List (ℕ × E) :=
  p.flatMap (fun a => q.map (fun b => (a.1 + b.1, B a.2 b.2)))

 theorem finiteVectorPolynomialEval_bilinear_right
    (B : E →L[ℝ] (E →L[ℝ] E)) (a : ℕ × E) (q : List (ℕ × E)) (t : ℝ) :
    finiteVectorPolynomialEval (q.map (fun b => (a.1 + b.1, B a.2 b.2))) t =
      B (t ^ a.1 • a.2) (finiteVectorPolynomialEval q t) := by
  induction q with
  | nil => simp only [List.map_nil, finiteVectorPolynomialEval_nil, map_zero]
  | cons b q ih =>
    rw [List.map_cons, finiteVectorPolynomialEval_cons, ih, finiteVectorPolynomialEval_cons, map_add]
    congr 1
    simp only [map_smul, smul_apply, pow_add, mul_smul]
    exact smul_comm (t ^ a.1) (t ^ b.1) (B a.2 b.2)

 theorem finiteVectorPolynomialEval_bilinear
    (B : E →L[ℝ] (E →L[ℝ] E)) (p q : List (ℕ × E)) (t : ℝ) :
    finiteVectorPolynomialEval (finiteVectorPolynomialBilinear B p q) t =
      B (finiteVectorPolynomialEval p t) (finiteVectorPolynomialEval q t) := by
  induction p with
  | nil => simp only [finiteVectorPolynomialBilinear, List.flatMap_nil,
      finiteVectorPolynomialEval_nil, map_zero, zero_apply]
  | cons a p ih =>
    change finiteVectorPolynomialEval
      (q.map (fun b => (a.1 + b.1, B a.2 b.2)) ++ finiteVectorPolynomialBilinear B p q) t = _
    rw [finiteVectorPolynomialEval_append, finiteVectorPolynomialEval_bilinear_right, ih,
      finiteVectorPolynomialEval_cons, map_add, add_apply]

end Hindman168
