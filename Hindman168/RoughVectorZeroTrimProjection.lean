import Hindman168.RoughVectorZeroTrim
import Hindman168.RoughVectorCoefficientEvaluationEquality

/-! Removing zero vector terms preserves COMPLETE scalar polynomials and
EVERY actual aggregate vector/scalar coefficient, not only sampled values. -/

namespace Hindman168
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rough_vector_zero_trim_projection (f : E →ₗ[ℝ] ℝ) (p : RoughVectorMvPolynomial σ E) :
    roughVectorMvProjection f (roughVectorMvZeroTrim p) = roughVectorMvProjection f p := by
  apply MvPolynomial.funext
  intro x
  rw [roughVectorMvProjection_eval,roughVectorMvProjection_eval,rough_vector_zero_trim_eval]

theorem rough_vector_zero_trim_scalar_coefficient (f : E →ₗ[ℝ] ℝ)
    (p : RoughVectorMvPolynomial σ E) (J : σ →₀ ℕ) :
    MvPolynomial.coeff J (roughVectorMvProjection f (roughVectorMvZeroTrim p)) =
      MvPolynomial.coeff J (roughVectorMvProjection f p) := by
  rw [rough_vector_zero_trim_projection]

theorem rough_vector_zero_trim_coefficient (p : RoughVectorMvPolynomial σ E) (J : σ →₀ ℕ) :
    roughVectorMvCoefficient (roughVectorMvZeroTrim p) J = roughVectorMvCoefficient p J := by
  have he := rough_vector_coefficient_difference_of_eval (roughVectorMvZeroTrim p) p []
    (fun x => by
      rw [rough_vector_zero_trim_eval]
      simp only [roughVectorMvEval,List.map_nil,List.sum_nil,sub_zero]) J
  simpa only [roughVectorMvCoefficient,List.map_nil,List.sum_nil,sub_zero] using he

end Hindman168
