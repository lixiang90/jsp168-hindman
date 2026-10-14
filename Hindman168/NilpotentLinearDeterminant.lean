import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Data.Real.Basic

namespace Hindman168

theorem nilpotent_linear_det_one_add {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (f : Module.End ℝ E) (hf : IsNilpotent f) :
    LinearMap.det (1+f) = 1 := by
  have h := LinearMap.eval_charpoly f (-1 : ℝ)
  rw [hf.charpoly_eq_X_pow_finrank, Polynomial.eval_pow, Polynomial.eval_X] at h
  have he : algebraMap ℝ (Module.End ℝ E) (-1 : ℝ)-f = (-1 : ℝ) • (1+f) := by
    simp only [map_neg, map_one, neg_one_smul]
    abel
  rw [he, LinearMap.det_smul] at h
  have hn : (-1 : ℝ)^Module.finrank ℝ E ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_left_cancel₀ hn (show (-1 : ℝ)^Module.finrank ℝ E * 1 =
    (-1 : ℝ)^Module.finrank ℝ E * LinearMap.det (1+f) by simpa only [mul_one] using h)).symm

end Hindman168
