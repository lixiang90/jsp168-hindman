import Hindman168.RoughVectorMvLinearMap

/-! ACTUAL product-model vector polynomial, retaining degree and evaluation. -/

namespace Hindman168
variable {σ E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def roughVectorMvPairPolynomial (p : RoughVectorMvPolynomial σ E)
    (q : RoughVectorMvPolynomial σ F) : RoughVectorMvPolynomial σ (E × F) :=
  roughVectorMvLinearMap (LinearMap.inl ℝ E F) p ++ roughVectorMvLinearMap (LinearMap.inr ℝ E F) q

theorem rough_vector_mv_pair_polynomial_degree (p : RoughVectorMvPolynomial σ E)
    (q : RoughVectorMvPolynomial σ F) (d : ℕ)
    (hp : RoughVectorMvDegreeLE p d) (hq : RoughVectorMvDegreeLE q d) :
    RoughVectorMvDegreeLE (roughVectorMvPairPolynomial p q) d :=
  roughVectorMvDegreeLE_append (roughVectorMvLinearMap_degree _ hp) (roughVectorMvLinearMap_degree _ hq)

theorem rough_vector_mv_pair_polynomial_eval (p : RoughVectorMvPolynomial σ E)
    (q : RoughVectorMvPolynomial σ F) (x : σ → ℝ) :
    roughVectorMvEval (roughVectorMvPairPolynomial p q) x = (roughVectorMvEval p x,roughVectorMvEval q x) := by
  unfold roughVectorMvPairPolynomial
  rw [roughVectorMvEval_append,roughVectorMvLinearMap_eval,roughVectorMvLinearMap_eval]
  simp only [LinearMap.inl_apply,LinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add]

end Hindman168
