import Hindman168.FiniteVectorPolynomialSums
import Hindman168.NativeLieGlobalProductLog

/-! The actual native dexp defect applied to finite polynomial curves is
represented by a finite polynomial list using only rational scalars and
the actual original adjoint differential, already identified with the
original native bracket. -/

namespace Hindman168
open Finset
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieRationalDefectPolynomial (p q : List (ℕ × E)) : List (ℕ × E) :=
  finiteVectorPolynomialSum (Group.nilpotencyClass G) (fun n =>
    finiteVectorPolynomialScale (-((-1 : ℚ) ^ (n + 1) / ((n + 2).factorial : ℚ)))
      (finiteVectorPolynomialAdPower (nativeLieAdjointDifferential (I := I) (G := G)) p q (n + 1)))

 theorem nativeLieRationalDefectPolynomial_eval (p q : List (ℕ × E)) (t : ℝ) :
    finiteVectorPolynomialEval (nativeLieRationalDefectPolynomial (I := I) (G := G) p q) t =
      nativeLieDexpDefect (I := I) (G := G) (finiteVectorPolynomialEval p t)
        (finiteVectorPolynomialEval q t) := by
  let v : E := finiteVectorPolynomialEval p t
  let w : E := finiteVectorPolynomialEval q t
  rw [nativeLieRationalDefectPolynomial, finiteVectorPolynomialEval_sum,
    nativeLieDexpDefect_finite_formula]
  simp only [finiteVectorPolynomialEval_scale, finiteVectorPolynomialEval_adPower,
    neg_apply, _root_.sum_apply, smul_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have hc : (((-1 : ℚ) ^ (n + 1) / ((n + 2).factorial : ℚ) : ℚ) : ℝ) =
      (-1 : ℝ) ^ (n + 1) / ((n + 2).factorial : ℝ) := by push_cast; rfl
  rw [nativeLieAdjointGenerator_eq_differential, neg_smul,
    ← Rat.cast_smul_eq_qsmul ℝ, hc]

omit [CompleteSpace E] [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G] in
 theorem nativeLieRationalDefectPolynomial_coefficients_mem
    (V : Submodule ℚ E)
    (hB : ∀ v ∈ V, ∀ w ∈ V, nativeLieAdjointDifferential (I := I) (G := G) v w ∈ V)
    {p q : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p)
    (hq : finiteVectorPolynomialCoefficientsMem V q) :
    finiteVectorPolynomialCoefficientsMem V
      (nativeLieRationalDefectPolynomial (I := I) (G := G) p q) := by
  apply finiteVectorPolynomialCoefficientsMem_sum
  intro n _
  apply finiteVectorPolynomialCoefficientsMem_scale
  exact finiteVectorPolynomialCoefficientsMem_adPower V _ hB hp hq (n + 1)

end Hindman168
