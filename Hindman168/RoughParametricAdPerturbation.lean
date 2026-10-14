import Hindman168.RoughParametricBilinearPerturbation

namespace Hindman168
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughParametricAdPerturbation (B : E →L[ℝ] (E →L[ℝ] E))
    (p₀ p₁ dp q₁ dq : RoughParametricCurve σ E) : ℕ → RoughParametricCurve σ E
  | 0 => dq
  | n+1 => roughParametricBilinearPerturbation B p₀ dp (roughParametricAd B p₁ q₁ n)
      (roughParametricAdPerturbation B p₀ p₁ dp q₁ dq n)

theorem rough_parametric_ad_perturbation_eval (B : E →L[ℝ] (E →L[ℝ] E))
    (p₀ p₁ dp q₀ q₁ dq : RoughParametricCurve σ E)
    (hp : ∀ x t, roughParametricEval dp x t = roughParametricEval p₁ x t-roughParametricEval p₀ x t)
    (hq : ∀ x t, roughParametricEval dq x t = roughParametricEval q₁ x t-roughParametricEval q₀ x t)
    (n : ℕ) : ∀ x t,
    roughParametricEval (roughParametricAdPerturbation B p₀ p₁ dp q₁ dq n) x t =
      roughParametricEval (roughParametricAd B p₁ q₁ n) x t-
        roughParametricEval (roughParametricAd B p₀ q₀ n) x t := by
  induction n with
  | zero => exact hq
  | succ n ih =>
      intro x t
      exact rough_parametric_bilinear_perturbation_eval B p₀ p₁ dp
        (roughParametricAd B p₀ q₀ n) (roughParametricAd B p₁ q₁ n)
        (roughParametricAdPerturbation B p₀ p₁ dp q₁ dq n) hp ih x t

theorem rough_parametric_ad_perturbation_weighted
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    {p₀ p₁ dp q₁ dq : RoughParametricCurve σ E} {k l : ℕ}
    (hp₀ : RoughParametricWeightedDegree F p₀ k) (hp₁ : RoughParametricWeightedDegree F p₁ k)
    (hq₁ : RoughParametricWeightedDegree F q₁ k)
    (hdp : RoughParametricWeightedDegree F dp l) (hdq : RoughParametricWeightedDegree F dq l)
    (n : ℕ) : RoughParametricWeightedDegree F (roughParametricAdPerturbation B p₀ p₁ dp q₁ dq n) l := by
  induction n with
  | zero => exact hdq
  | succ n ih =>
      exact rough_parametric_bilinear_perturbation_weighted F hF B hB hp₀
        (rough_parametric_weighted_ad F hF B hB hp₁ hq₁ n) hdp ih

end Hindman168
