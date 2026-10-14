import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Matrix.Normed

/-! Smoothness of actual finite matrix operations in the entrywise real norm.
No normed-ring structure for matrix multiplication is assumed: its entries
are proved smooth directly by finite scalar sums and products. -/

namespace Hindman168
open Matrix
open scoped ContDiff Matrix.Norms.Elementwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {r : ℕ∞ω}

 theorem contDiff_matrix_mul {f g : E → Matrix (Fin n) (Fin n) ℝ}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) :
    ContDiff ℝ r (fun x => f x * g x) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ =>
    ((contDiff_apply_apply ℝ ℝ i k).comp hf).mul ((contDiff_apply_apply ℝ ℝ k j).comp hg)

 theorem contDiff_matrix_pow {f : E → Matrix (Fin n) (Fin n) ℝ}
    (hf : ContDiff ℝ r f) (k : ℕ) : ContDiff ℝ r (fun x => f x ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using (contDiff_const :
      ContDiff ℝ r (fun _ : E => (1 : Matrix (Fin n) (Fin n) ℝ)))
  | succ k ih => simpa only [pow_succ] using contDiff_matrix_mul ih hf

 theorem contDiff_matrix_det {f : E → Matrix (Fin n) (Fin n) ℝ}
    (hf : ContDiff ℝ r f) : ContDiff ℝ r (fun x => (f x).det) := by
  classical
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul
    (contDiff_prod fun i _ => (contDiff_apply_apply ℝ ℝ (σ i) i).comp hf)

 theorem contDiff_matrix_adjugate {f : E → Matrix (Fin n) (Fin n) ℝ}
    (hf : ContDiff ℝ r f) : ContDiff ℝ r (fun x => (f x).adjugate) := by
  classical
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.adjugate_apply]
  apply contDiff_matrix_det
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro b
  by_cases h : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simpa only [Matrix.updateRow_ne h, Function.comp_def] using (contDiff_apply_apply ℝ ℝ a b).comp hf

end Hindman168
