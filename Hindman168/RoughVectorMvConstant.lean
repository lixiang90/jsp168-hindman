import Hindman168.RoughVectorWeightedDegree

namespace Hindman168
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughVectorMvConstant (v : E) : RoughVectorMvPolynomial σ E := [(1,v)]

theorem rough_vector_constant_eval (v : E) (x : σ → ℝ) :
    roughVectorMvEval (roughVectorMvConstant v) x = v := by
  simp only [roughVectorMvConstant,roughVectorMvEval,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,map_one,one_smul,add_zero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem rough_vector_constant_degree (v : E) :
    RoughVectorMvDegreeLE (roughVectorMvConstant (σ := σ) v) 0 := by
  intro a ha
  have he := List.mem_singleton.mp ha
  subst a
  simp only [MvPolynomial.totalDegree_one,le_refl]

theorem rough_vector_constant_weighted (F : ℕ → Submodule ℝ E) {k : ℕ} {v : E}
    (hv : v ∈ F k) :
    RoughVectorMvWeightedDegree F (roughVectorMvConstant (σ := σ) v) k := by
  intro a ha
  have he := List.mem_singleton.mp ha
  subst a
  simpa only [MvPolynomial.totalDegree_one,Nat.zero_add] using hv

theorem rough_vector_constant_projection (ell : E →ₗ[ℝ] ℝ) (v : E) :
    roughVectorMvProjection ell (roughVectorMvConstant (σ := σ) v) = MvPolynomial.C (ell v) := by
  simp only [roughVectorMvConstant,roughVectorMvProjection,one_mul,add_zero]

end Hindman168
