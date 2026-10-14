import Hindman168.RoughVectorMvCoefficients
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! EXACT actual vector coefficient difference identities follow from
actual evaluation differences on every real assignment. -/

namespace Hindman168
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rough_vector_coefficient_difference_of_eval
    (q p r : RoughVectorMvPolynomial σ E)
    (h : ∀ x : σ → ℝ, roughVectorMvEval q x = roughVectorMvEval p x-roughVectorMvEval r x)
    (J : σ →₀ ℕ) : roughVectorMvCoefficient q J = roughVectorMvCoefficient p J-roughVectorMvCoefficient r J := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℝ
    (roughVectorMvCoefficient q J-(roughVectorMvCoefficient p J-roughVectorMvCoefficient r J))).mp
  intro ell
  have he : roughVectorMvProjection ell q = roughVectorMvProjection ell p-roughVectorMvProjection ell r := by
    apply MvPolynomial.funext
    intro x
    rw [roughVectorMvProjection_eval,map_sub,roughVectorMvProjection_eval,roughVectorMvProjection_eval,h x,map_sub]
  rw [map_sub,map_sub,rough_vector_coefficient_projection,rough_vector_coefficient_projection,
    rough_vector_coefficient_projection,he,MvPolynomial.coeff_sub,sub_self]

end Hindman168
