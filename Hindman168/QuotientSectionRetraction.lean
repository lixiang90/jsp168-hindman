import Hindman168.ClosedFiniteRealQuotientSection

namespace Hindman168

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (V : Submodule ℝ E) [IsClosed (V : Set E)]

noncomputable def finiteRealQuotientSectionRetraction : E →L[ℝ] V := by
  let P : E →ₗ[ℝ] E := LinearMap.id -
    (finiteRealQuotientSection V).toLinearMap.comp (finiteRealQuotientProjection V).toLinearMap
  have hP : ∀ x, P x ∈ V := by
    intro x
    apply (Submodule.Quotient.mk_eq_zero V).mp
    change finiteRealQuotientProjection V (P x) = 0
    simp only [P, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, map_sub, finiteRealQuotientSection_right, sub_self]
  exact (P.codRestrict V hP).toContinuousLinearMap

theorem finiteRealQuotientSectionRetraction_val (x : E) :
    (finiteRealQuotientSectionRetraction V x : E) =
      x - finiteRealQuotientSection V (finiteRealQuotientProjection V x) := rfl

theorem finiteRealQuotientSectionRetraction_subtype (x : V) :
    finiteRealQuotientSectionRetraction V (x : E) = x := by
  apply Subtype.ext
  rw [finiteRealQuotientSectionRetraction_val]
  have hx : finiteRealQuotientProjection V (x : E) = 0 :=
    (Submodule.Quotient.mk_eq_zero V).mpr x.property
  rw [hx, map_zero, sub_zero]

end Hindman168
