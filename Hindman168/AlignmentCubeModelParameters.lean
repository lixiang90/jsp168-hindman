import Hindman168.AlignmentCubeExponentPolynomial

namespace Hindman168
open MvPolynomial

noncomputable def alignmentCubeBasePolynomial (M Y r rv s : ℝ) : MvPolynomial Bool ℝ :=
  C (Y + (r - rv) / M) + X false + C (s / M) * X true

noncomputable def alignmentCubeIncrementPolynomial (M q rho : ℝ) : MvPolynomial Bool ℝ :=
  C (q / M) - C (rho / M) * X true

theorem alignmentCubeBasePolynomial_degree (M Y r rv s : ℝ) :
    (alignmentCubeBasePolynomial M Y r rv s).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_add _ _).trans (by simp only [totalDegree_C, totalDegree_X]; decide)
  · exact (totalDegree_mul _ _).trans (by simp)

theorem alignmentCubeIncrementPolynomial_degree (M q rho : ℝ) :
    (alignmentCubeIncrementPolynomial M q rho).totalDegree ≤ 1 := by
  apply (totalDegree_sub _ _).trans
  apply max_le (by simp)
  exact (totalDegree_mul _ _).trans (by simp)

theorem alignmentCubeBasePolynomial_eval (M Y r rv s x t : ℝ) :
    eval (fun b => if b then t else x) (alignmentCubeBasePolynomial M Y r rv s) =
      x + Y + (r + t * s - rv) / M := by
  simp only [alignmentCubeBasePolynomial, map_add, map_mul, eval_C, eval_X,
    Bool.false_eq_true, ↓reduceIte]
  ring

theorem alignmentCubeIncrementPolynomial_eval (M q rho x t : ℝ) :
    eval (fun b => if b then t else x) (alignmentCubeIncrementPolynomial M q rho) =
      (q - t * rho) / M := by
  simp only [alignmentCubeIncrementPolynomial, map_sub, map_mul, eval_C, eval_X,
    ↓reduceIte]
  ring

theorem alignmentCubeBasePolynomial_integral_eval (M Y r rv s x t k : ℤ)
    (hM : M ≠ 0) (hk : M * k = r + t * s - rv) :
    eval (fun b => if b then (t : ℝ) else (x : ℝ))
      (alignmentCubeBasePolynomial M Y r rv s) = ((x + Y + k : ℤ) : ℝ) := by
  rw [alignmentCubeBasePolynomial_eval]
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have h : ((r : ℝ) + t * s - rv) / M = k := by
    apply (div_eq_iff hm).mpr
    exact_mod_cast hk.symm.trans (mul_comm M k)
  simp only [h, Int.cast_add]

theorem alignmentCubeIncrementPolynomial_integral_eval (M q rho x t delta : ℤ)
    (hM : M ≠ 0) (hd : M * delta = q - t * rho) :
    eval (fun b => if b then (t : ℝ) else (x : ℝ))
      (alignmentCubeIncrementPolynomial M q rho) = (delta : ℝ) := by
  rw [alignmentCubeIncrementPolynomial_eval]
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  apply (div_eq_iff hm).mpr
  exact_mod_cast hd.symm.trans (mul_comm M delta)

end Hindman168
