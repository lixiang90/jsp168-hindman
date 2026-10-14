import Hindman168.RoughParametricEvaluation
import Hindman168.RoughParametricWeightedPicard

namespace Hindman168
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughParametricBilinearPerturbation (B : E →L[ℝ] (E →L[ℝ] E))
    (p₀ dp q₁ dq : RoughParametricCurve σ E) : RoughParametricCurve σ E :=
  roughParametricBilinear B dp q₁ ++ roughParametricBilinear B p₀ dq

theorem rough_parametric_bilinear_perturbation_eval (B : E →L[ℝ] (E →L[ℝ] E))
    (p₀ p₁ dp q₀ q₁ dq : RoughParametricCurve σ E)
    (hp : ∀ x t, roughParametricEval dp x t = roughParametricEval p₁ x t-roughParametricEval p₀ x t)
    (hq : ∀ x t, roughParametricEval dq x t = roughParametricEval q₁ x t-roughParametricEval q₀ x t)
    (x : σ → ℝ) (t : ℝ) :
    roughParametricEval (roughParametricBilinearPerturbation B p₀ dp q₁ dq) x t =
      roughParametricEval (roughParametricBilinear B p₁ q₁) x t-
        roughParametricEval (roughParametricBilinear B p₀ q₀) x t := by
  simp only [roughParametricBilinearPerturbation, rough_parametric_eval_append,
    rough_parametric_eval_bilinear, hp, hq, map_sub, sub_apply]
  abel

theorem rough_parametric_bilinear_perturbation_weighted
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    {p₀ dp q₁ dq : RoughParametricCurve σ E} {k l : ℕ}
    (hp : RoughParametricWeightedDegree F p₀ k) (hq : RoughParametricWeightedDegree F q₁ k)
    (hdp : RoughParametricWeightedDegree F dp l) (hdq : RoughParametricWeightedDegree F dq l) :
    RoughParametricWeightedDegree F (roughParametricBilinearPerturbation B p₀ dp q₁ dq) l := by
  apply rough_parametric_weighted_append
  · exact rough_parametric_weighted_mono F hF
      (rough_parametric_weighted_bilinear F hF B hB hdp hq) (Nat.le_add_right l k)
  · exact rough_parametric_weighted_mono F hF
      (rough_parametric_weighted_bilinear F hF B hB hp hdq) (Nat.le_add_left l k)

end Hindman168
