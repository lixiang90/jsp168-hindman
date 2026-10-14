import Hindman168.RoughParametricCurve

namespace Hindman168
open MeasureTheory
open scoped BigOperators Interval
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughParametricEval (p : RoughParametricCurve σ E) (x : σ → ℝ) (t : ℝ) : E :=
  finiteVectorPolynomialEval (roughParametricSpecialize p x) t

theorem rough_parametric_eval_nil (x : σ → ℝ) (t : ℝ) :
    roughParametricEval ([] : RoughParametricCurve σ E) x t = 0 := rfl

theorem rough_parametric_eval_singleton (p : RoughVectorMvPolynomial σ E) (n : ℕ)
    (x : σ → ℝ) (t : ℝ) : roughParametricEval [(n,p)] x t = t^n • roughVectorMvEval p x :=
  finiteVectorPolynomialEval_singleton _ _ _

theorem rough_parametric_eval_append (p q : RoughParametricCurve σ E) (x : σ → ℝ) (t : ℝ) :
    roughParametricEval (p++q) x t = roughParametricEval p x t+roughParametricEval q x t := by
  simp only [roughParametricEval, roughParametricSpecialize, List.map_append,
    finiteVectorPolynomialEval_append]

theorem rough_parametric_eval_bilinear (B : E →L[ℝ] (E →L[ℝ] E))
    (p q : RoughParametricCurve σ E) (x : σ → ℝ) (t : ℝ) :
    roughParametricEval (roughParametricBilinear B p q) x t =
      B (roughParametricEval p x t) (roughParametricEval q x t) := by
  rw [roughParametricEval, roughParametricSpecialize_bilinear, finiteVectorPolynomialEval_bilinear]
  rfl

theorem rough_parametric_eval_sum (n : ℕ) (p : ℕ → RoughParametricCurve σ E)
    (x : σ → ℝ) (t : ℝ) : roughParametricEval (roughParametricSum n p) x t =
      ∑ j ∈ Finset.range n, roughParametricEval (p j) x t := by
  rw [roughParametricEval, roughParametricSpecialize_sum, finiteVectorPolynomialEval_sum]
  rfl

theorem rough_parametric_eval_continuous (p : RoughParametricCurve σ E) (x : σ → ℝ) :
    Continuous (roughParametricEval p x) := finiteVectorPolynomialEval_continuous _

theorem rough_parametric_eval_endpoint (p : RoughParametricCurve σ E) (x : σ → ℝ) :
    roughVectorMvEval (roughParametricEndpoint p) x = roughParametricEval p x 1 :=
  roughParametricEndpoint_eval _ _

variable [Module ℚ E]

theorem rough_parametric_eval_scale (r : ℚ) (p : RoughParametricCurve σ E)
    (x : σ → ℝ) (t : ℝ) : roughParametricEval (roughParametricScale r p) x t =
      (r : ℝ) • roughParametricEval p x t := by
  rw [roughParametricEval, roughParametricSpecialize_scale, finiteVectorPolynomialEval_scale]
  exact (Rat.cast_smul_eq_qsmul ℝ r _).symm

variable [CompleteSpace E]

theorem rough_parametric_eval_primitive (p : RoughParametricCurve σ E) (x : σ → ℝ) (t : ℝ) :
    roughParametricEval (roughParametricPrimitive p) x t =
      ∫ s in (0 : ℝ)..t, roughParametricEval p x s := by
  rw [roughParametricEval, roughParametricSpecialize_primitive, finiteVectorPolynomialEval_primitive]
  rfl

theorem rough_parametric_primitive_difference
    (p₀ p₁ dp : RoughParametricCurve σ E)
    (he : ∀ x t, roughParametricEval dp x t = roughParametricEval p₁ x t-roughParametricEval p₀ x t)
    (x : σ → ℝ) (t : ℝ) :
    roughParametricEval (roughParametricPrimitive dp) x t =
      roughParametricEval (roughParametricPrimitive p₁) x t-
        roughParametricEval (roughParametricPrimitive p₀) x t := by
  simp only [rough_parametric_eval_primitive, he]
  exact intervalIntegral.integral_sub
    ((rough_parametric_eval_continuous p₁ x).intervalIntegrable 0 t)
    ((rough_parametric_eval_continuous p₀ x).intervalIntegrable 0 t)

end Hindman168
