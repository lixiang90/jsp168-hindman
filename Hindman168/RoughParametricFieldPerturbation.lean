import Hindman168.RoughParametricDefectPerturbation

namespace Hindman168
open scoped BigOperators
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughParametricDefectPowerPerturbation (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    (p₀ p₁ dp q₁ dq : RoughParametricCurve σ E) : ℕ → RoughParametricCurve σ E
  | 0 => dq
  | n+1 => roughParametricDefectPerturbation B s p₀ p₁ dp
      (roughParametricDefectPower B s p₁ q₁ n)
      (roughParametricDefectPowerPerturbation B s p₀ p₁ dp q₁ dq n)

noncomputable def roughParametricFieldPerturbation (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    (p₀ p₁ dp q₁ dq : RoughParametricCurve σ E) : RoughParametricCurve σ E :=
  roughParametricSum s (roughParametricDefectPowerPerturbation B s p₀ p₁ dp q₁ dq)

theorem rough_parametric_defect_power_perturbation_weighted
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    (s : ℕ) {p₀ p₁ dp q₁ dq : RoughParametricCurve σ E} {k l : ℕ}
    (hp₀ : RoughParametricWeightedDegree F p₀ k) (hp₁ : RoughParametricWeightedDegree F p₁ k)
    (hq₁ : RoughParametricWeightedDegree F q₁ k)
    (hdp : RoughParametricWeightedDegree F dp l) (hdq : RoughParametricWeightedDegree F dq l)
    (n : ℕ) :
    RoughParametricWeightedDegree F (roughParametricDefectPowerPerturbation B s p₀ p₁ dp q₁ dq n) l := by
  induction n with
  | zero => exact hdq
  | succ n ih =>
      exact rough_parametric_defect_perturbation_weighted F hF B hB s hp₀ hp₁
        (rough_parametric_weighted_defect_power F hF B hB s hp₁ hq₁ n) hdp ih

theorem rough_parametric_field_perturbation_weighted
    (F : ℕ → Submodule ℝ E) (hF : Antitone F) (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    (s : ℕ) {p₀ p₁ dp q₁ dq : RoughParametricCurve σ E} {k l : ℕ}
    (hp₀ : RoughParametricWeightedDegree F p₀ k) (hp₁ : RoughParametricWeightedDegree F p₁ k)
    (hq₁ : RoughParametricWeightedDegree F q₁ k)
    (hdp : RoughParametricWeightedDegree F dp l) (hdq : RoughParametricWeightedDegree F dq l) :
    RoughParametricWeightedDegree F (roughParametricFieldPerturbation B s p₀ p₁ dp q₁ dq) l := by
  apply rough_parametric_weighted_sum
  intro n _
  exact rough_parametric_defect_power_perturbation_weighted F hF B hB s hp₀ hp₁ hq₁ hdp hdq n

variable [Module ℚ E]

theorem rough_parametric_defect_power_perturbation_eval (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    (p₀ p₁ dp q₀ q₁ dq : RoughParametricCurve σ E)
    (hp : ∀ x t, roughParametricEval dp x t = roughParametricEval p₁ x t-roughParametricEval p₀ x t)
    (hq : ∀ x t, roughParametricEval dq x t = roughParametricEval q₁ x t-roughParametricEval q₀ x t)
    (n : ℕ) : ∀ x t,
    roughParametricEval (roughParametricDefectPowerPerturbation B s p₀ p₁ dp q₁ dq n) x t =
      roughParametricEval (roughParametricDefectPower B s p₁ q₁ n) x t-
        roughParametricEval (roughParametricDefectPower B s p₀ q₀ n) x t := by
  induction n with
  | zero => exact hq
  | succ n ih =>
      exact rough_parametric_defect_perturbation_eval B s p₀ p₁ dp
        (roughParametricDefectPower B s p₀ q₀ n) (roughParametricDefectPower B s p₁ q₁ n)
        (roughParametricDefectPowerPerturbation B s p₀ p₁ dp q₁ dq n) hp ih

theorem rough_parametric_field_perturbation_eval (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    (p₀ p₁ dp q₀ q₁ dq : RoughParametricCurve σ E)
    (hp : ∀ x t, roughParametricEval dp x t = roughParametricEval p₁ x t-roughParametricEval p₀ x t)
    (hq : ∀ x t, roughParametricEval dq x t = roughParametricEval q₁ x t-roughParametricEval q₀ x t) :
    ∀ x t, roughParametricEval (roughParametricFieldPerturbation B s p₀ p₁ dp q₁ dq) x t =
      roughParametricEval (roughParametricField B s p₁ q₁) x t-
        roughParametricEval (roughParametricField B s p₀ q₀) x t := by
  intro x t
  simp only [roughParametricFieldPerturbation, roughParametricField, rough_parametric_eval_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  exact rough_parametric_defect_power_perturbation_eval B s p₀ p₁ dp q₀ q₁ dq hp hq n x t

end Hindman168
