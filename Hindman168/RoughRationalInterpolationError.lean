import Hindman168.RoughRationalInterpolation

namespace Hindman168
open Polynomial

theorem rough_rational_interpolation_value_error {q H : ℕ}
    (hq : 0 < q) (hH : 2 * q + 2 ≤ H) (T : ℝ[X]) (hT : T.natDegree ≤ q)
    (values : Fin (q + 1) → ℤ) (eps : ℝ) (heps : 0 ≤ eps)
    (herr : ∀ i, |(values i : ℝ) - T.eval (roughInterpolationNode q H i : ℝ)| ≤ eps)
    (z : ℚ) (hz : 0 ≤ z) (hzH : z ≤ ((H - 1 : ℕ) : ℚ)) :
    |(((roughRationalInterpolation q H values).eval z : ℚ) : ℝ) - T.eval (z : ℝ)| ≤
      roughInterpolationConstant q * eps := by
  have hb := rough_interpolation_uniform_value_error hq hH T hT (fun i => (values i : ℝ))
    eps heps herr (z : ℝ) (by exact_mod_cast hz) (by exact_mod_cast hzH)
  rw [← roughRationalInterpolation_map_real hq hH values] at hb
  have hv := eval_map_apply (p := roughRationalInterpolation q H values) (Rat.castHom ℝ) z
  change ((roughRationalInterpolation q H values).map (Rat.castHom ℝ)).eval (z : ℝ) =
    (((roughRationalInterpolation q H values).eval z : ℚ) : ℝ) at hv
  rwa [hv] at hb

theorem rough_rational_interpolation_derivative_error {q H : ℕ}
    (hq : 0 < q) (hH : 2 * q + 2 ≤ H) (T : ℝ[X]) (hT : T.natDegree ≤ q)
    (values : Fin (q + 1) → ℤ) (eps : ℝ) (heps : 0 ≤ eps)
    (herr : ∀ i, |(values i : ℝ) - T.eval (roughInterpolationNode q H i : ℝ)| ≤ eps)
    (j : ℕ) (hj : j ≤ q) (S : ℝ) (a : ℚ) (hS : 0 ≤ S) (ha : |(a : ℝ)| ≤ 2 * S) :
    |(((derivative^[j] (roughRationalInterpolation q H values)).eval a : ℚ) : ℝ) -
      (derivative^[j] T).eval (a : ℝ)| ≤
      roughInterpolationConstant q * eps * (1 + 2 * S) ^ q := by
  have hb := rough_interpolation_uniform_derivative_error hq hH T hT (fun i => (values i : ℝ))
    eps heps herr j hj S (a : ℝ) hS ha
  rw [← roughRationalInterpolation_map_real hq hH values,
    iterate_derivative_sub, eval_sub, iterate_derivative_map] at hb
  have hv := eval_map_apply (p := derivative^[j] (roughRationalInterpolation q H values))
    (Rat.castHom ℝ) a
  change ((derivative^[j] (roughRationalInterpolation q H values)).map (Rat.castHom ℝ)).eval (a : ℝ) =
    (((derivative^[j] (roughRationalInterpolation q H values)).eval a : ℚ) : ℝ) at hv
  rwa [hv] at hb

end Hindman168
