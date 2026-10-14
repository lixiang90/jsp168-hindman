import Hindman168.RoughVectorMonomialCollection
import Hindman168.RoughVectorMvProjectionNaturality

/-! Actual aggregated coefficients construct a genuine vector polynomial
inside the SAME original real submodule. Original evaluations and complete
scalar polynomials are preserved after its actual inclusion. -/

namespace Hindman168
open scoped Classical
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughVectorMvSubmodulePolynomial (S : Submodule ℝ E)
    (p : RoughVectorMvPolynomial σ E) (hP : ∀ J, roughVectorMvCoefficient p J ∈ S) :
    RoughVectorMvPolynomial σ S :=
  (roughVectorMvSupport p).toList.map
    (fun J => (MvPolynomial.monomial J 1,⟨roughVectorMvCoefficient p J,hP J⟩))

theorem rough_vector_submodule_polynomial_inclusion (S : Submodule ℝ E)
    (p : RoughVectorMvPolynomial σ E) (hP : ∀ J, roughVectorMvCoefficient p J ∈ S) :
    roughVectorMvLinearMap S.subtype (roughVectorMvSubmodulePolynomial S p hP) = roughVectorMvCollect p := by
  simp only [roughVectorMvLinearMap,roughVectorMvSubmodulePolynomial,roughVectorMvCollect,List.map_map]
  rfl

theorem rough_vector_submodule_polynomial_eval (S : Submodule ℝ E)
    (p : RoughVectorMvPolynomial σ E) (hP : ∀ J, roughVectorMvCoefficient p J ∈ S) (x : σ → ℝ) :
    S.subtype (roughVectorMvEval (roughVectorMvSubmodulePolynomial S p hP) x) = roughVectorMvEval p x := by
  rw [← roughVectorMvLinearMap_eval,rough_vector_submodule_polynomial_inclusion,rough_vector_collect_eval]

theorem rough_vector_submodule_polynomial_degree (S : Submodule ℝ E)
    (p : RoughVectorMvPolynomial σ E) (hP : ∀ J, roughVectorMvCoefficient p J ∈ S)
    {d : ℕ} (hp : RoughVectorMvDegreeLE p d) :
    RoughVectorMvDegreeLE (roughVectorMvSubmodulePolynomial S p hP) d := by
  rintro a ha
  obtain ⟨J,hJ,rfl⟩ := List.mem_map.mp ha
  exact (MvPolynomial.totalDegree_monomial_le J (1 : ℝ)).trans
    (rough_vector_support_degree hp J (Finset.mem_toList.mp hJ))

theorem rough_vector_submodule_polynomial_projection (S : Submodule ℝ E)
    (p : RoughVectorMvPolynomial σ E) (hP : ∀ J, roughVectorMvCoefficient p J ∈ S) (ell : E →ₗ[ℝ] ℝ) :
    roughVectorMvProjection (ell.comp S.subtype) (roughVectorMvSubmodulePolynomial S p hP) =
      roughVectorMvProjection ell p := by
  rw [← roughVectorMvProjection_linearMap,rough_vector_submodule_polynomial_inclusion,rough_vector_collect_projection]

end Hindman168
