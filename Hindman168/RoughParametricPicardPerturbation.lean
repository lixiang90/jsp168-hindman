import Hindman168.RoughParametricFieldPerturbation

namespace Hindman168
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughParametricPicardPerturbation (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    (w₀ w₁ dw u₀ u₁ du : RoughVectorMvPolynomial σ E) : ℕ → RoughParametricCurve σ E
  | 0 => [(0,du)]
  | n+1 => [(0,du)] ++ roughParametricPrimitive (roughParametricFieldPerturbation B s
      (roughParametricPicard B s w₀ u₀ n) (roughParametricPicard B s w₁ u₁ n)
      (roughParametricPicardPerturbation B s w₀ w₁ dw u₀ u₁ du n) [(0,w₁)] [(0,dw)])

theorem rough_parametric_picard_perturbation_weighted
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    (s : ℕ) {w₀ w₁ dw u₀ u₁ du : RoughVectorMvPolynomial σ E} {k l : ℕ}
    (hw₀ : RoughVectorMvWeightedDegree F w₀ k) (hw₁ : RoughVectorMvWeightedDegree F w₁ k)
    (hu₀ : RoughVectorMvWeightedDegree F u₀ k) (hu₁ : RoughVectorMvWeightedDegree F u₁ k)
    (hdw : RoughVectorMvWeightedDegree F dw l) (hdu : RoughVectorMvWeightedDegree F du l) (n : ℕ) :
    RoughParametricWeightedDegree F (roughParametricPicardPerturbation B s w₀ w₁ dw u₀ u₁ du n) l := by
  induction n with
  | zero => exact rough_parametric_weighted_singleton F hdu 0
  | succ n ih =>
      apply rough_parametric_weighted_append F (rough_parametric_weighted_singleton F hdu 0)
      apply rough_parametric_weighted_primitive
      exact rough_parametric_field_perturbation_weighted F hF B hB s
        (rough_parametric_weighted_picard F hF B hB s hw₀ hu₀ n)
        (rough_parametric_weighted_picard F hF B hB s hw₁ hu₁ n)
        (rough_parametric_weighted_singleton F hw₁ 0) ih (rough_parametric_weighted_singleton F hdw 0)

variable [Module ℚ E] [CompleteSpace E]

theorem rough_parametric_picard_perturbation_eval (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    (w₀ w₁ dw u₀ u₁ du : RoughVectorMvPolynomial σ E)
    (hw : ∀ x, roughVectorMvEval dw x = roughVectorMvEval w₁ x-roughVectorMvEval w₀ x)
    (hu : ∀ x, roughVectorMvEval du x = roughVectorMvEval u₁ x-roughVectorMvEval u₀ x)
    (n : ℕ) : ∀ x t,
    roughParametricEval (roughParametricPicardPerturbation B s w₀ w₁ dw u₀ u₁ du n) x t =
      roughParametricEval (roughParametricPicard B s w₁ u₁ n) x t-
        roughParametricEval (roughParametricPicard B s w₀ u₀ n) x t := by
  have hw' : ∀ x t, roughParametricEval [(0,dw)] x t =
      roughParametricEval [(0,w₁)] x t-roughParametricEval [(0,w₀)] x t := by
    intro x t
    simpa only [rough_parametric_eval_singleton, pow_zero, one_smul] using hw x
  induction n with
  | zero =>
      intro x t
      simpa only [roughParametricPicardPerturbation, roughParametricPicard,
        rough_parametric_eval_singleton, pow_zero, one_smul] using hu x
  | succ n ih =>
      intro x t
      have he := rough_parametric_primitive_difference
        (roughParametricField B s (roughParametricPicard B s w₀ u₀ n) [(0,w₀)])
        (roughParametricField B s (roughParametricPicard B s w₁ u₁ n) [(0,w₁)])
        (roughParametricFieldPerturbation B s (roughParametricPicard B s w₀ u₀ n)
          (roughParametricPicard B s w₁ u₁ n)
          (roughParametricPicardPerturbation B s w₀ w₁ dw u₀ u₁ du n) [(0,w₁)] [(0,dw)])
        (rough_parametric_field_perturbation_eval B s _ _ _ _ _ _ ih hw') x t
      simp only [roughParametricPicardPerturbation, roughParametricPicard,
        rough_parametric_eval_append, rough_parametric_eval_singleton, pow_zero, one_smul]
      rw [he, hu x]
      abel

end Hindman168
