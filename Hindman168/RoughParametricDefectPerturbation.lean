import Hindman168.RoughParametricAdPerturbation

namespace Hindman168
open scoped BigOperators
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughParametricDefectPerturbation (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    (p₀ p₁ dp q₁ dq : RoughParametricCurve σ E) : RoughParametricCurve σ E :=
  roughParametricSum s (fun n =>
    roughParametricScale (-((-1 : ℚ)^(n+1)/((n+2).factorial : ℚ)))
      (roughParametricAdPerturbation B p₀ p₁ dp q₁ dq (n+1)))

theorem rough_parametric_defect_perturbation_weighted
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    (s : ℕ) {p₀ p₁ dp q₁ dq : RoughParametricCurve σ E} {k l : ℕ}
    (hp₀ : RoughParametricWeightedDegree F p₀ k) (hp₁ : RoughParametricWeightedDegree F p₁ k)
    (hq₁ : RoughParametricWeightedDegree F q₁ k)
    (hdp : RoughParametricWeightedDegree F dp l) (hdq : RoughParametricWeightedDegree F dq l) :
    RoughParametricWeightedDegree F (roughParametricDefectPerturbation B s p₀ p₁ dp q₁ dq) l := by
  apply rough_parametric_weighted_sum
  intro n _
  apply rough_parametric_weighted_scale
  exact rough_parametric_ad_perturbation_weighted F hF B hB hp₀ hp₁ hq₁ hdp hdq (n+1)

variable [Module ℚ E]

theorem rough_parametric_defect_perturbation_eval (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    (p₀ p₁ dp q₀ q₁ dq : RoughParametricCurve σ E)
    (hp : ∀ x t, roughParametricEval dp x t = roughParametricEval p₁ x t-roughParametricEval p₀ x t)
    (hq : ∀ x t, roughParametricEval dq x t = roughParametricEval q₁ x t-roughParametricEval q₀ x t) :
    ∀ x t, roughParametricEval (roughParametricDefectPerturbation B s p₀ p₁ dp q₁ dq) x t =
      roughParametricEval (roughParametricDefect B s p₁ q₁) x t-
        roughParametricEval (roughParametricDefect B s p₀ q₀) x t := by
  intro x t
  simp only [roughParametricDefectPerturbation, roughParametricDefect,
    rough_parametric_eval_sum, rough_parametric_eval_scale]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [rough_parametric_ad_perturbation_eval B p₀ p₁ dp q₀ q₁ dq hp hq, smul_sub]

end Hindman168
