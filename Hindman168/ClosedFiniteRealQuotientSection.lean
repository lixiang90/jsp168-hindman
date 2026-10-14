import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Actual finite real submodule quotients have constructed continuous
linear sections. Algebraic projectivity provides a right inverse, and
actual finite dimension proves continuity. No section is assumed. -/

namespace Hindman168

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (V : Submodule ℝ E) [IsClosed (V : Set E)]

noncomputable def finiteRealQuotientProjection : E →L[ℝ] E ⧸ V :=
  V.mkQ.toContinuousLinearMap

omit [IsClosed (V : Set E)] in
theorem finiteRealQuotientProjection_apply (v : E) :
    finiteRealQuotientProjection V v = Submodule.Quotient.mk v := rfl

theorem finiteRealQuotientSection_exists :
    ∃ s : (E ⧸ V) →L[ℝ] E, ∀ x, finiteRealQuotientProjection V (s x) = x := by
  obtain ⟨s, hs⟩ := V.mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr V.mkQ_surjective)
  refine ⟨s.toContinuousLinearMap, ?_⟩
  intro x
  exact congrArg (fun f : (E ⧸ V) →ₗ[ℝ] E ⧸ V => f x) hs

noncomputable def finiteRealQuotientSection : (E ⧸ V) →L[ℝ] E :=
  Classical.choose (finiteRealQuotientSection_exists V)

theorem finiteRealQuotientSection_right (x : E ⧸ V) :
    finiteRealQuotientProjection V (finiteRealQuotientSection V x) = x :=
  Classical.choose_spec (finiteRealQuotientSection_exists V) x

end Hindman168
