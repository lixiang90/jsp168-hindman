import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Ring

namespace Hindman168
open NNReal

theorem bounded_real_mul_lipschitz {X : Type*} [PseudoMetricSpace X] (f g : X → ℝ)
    {Lf Lg Bf Bg : ℝ≥0} (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hbf : ∀ x, |f x| ≤ Bf) (hbg : ∀ x, |g x| ≤ Bg) :
    LipschitzWith (Bf * Lg + Bg * Lf) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hdf : |f x - f y| ≤ (Lf : ℝ) * dist x y := hf.dist_le_mul x y
  have hdg : |g x - g y| ≤ (Lg : ℝ) * dist x y := hg.dist_le_mul x y
  change |f x * g x - f y * g y| ≤ _
  calc
    _ = |f x * (g x - g y) + (f x - f y) * g y| := congrArg abs (by ring)
    _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
      simpa only [abs_mul] using abs_add_le (f x * (g x - g y)) ((f x - f y) * g y)
    _ ≤ (Bf : ℝ) * ((Lg : ℝ) * dist x y) + ((Lf : ℝ) * dist x y) * (Bg : ℝ) :=
      add_le_add (mul_le_mul (hbf x) hdg (abs_nonneg _) Bf.coe_nonneg)
        (mul_le_mul hdf (hbg y) (abs_nonneg _) (mul_nonneg Lf.coe_nonneg dist_nonneg))
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

end Hindman168
