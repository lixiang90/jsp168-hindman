import Mathlib.MeasureTheory.Function.Jacobian

namespace Hindman168
open MeasureTheory Measure Set

/-- Actual global change of variables with determinant one; no invariant
measure conclusion is assumed from the topology of the homeomorphism. -/
theorem smooth_unit_jacobian_map_addHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ] (T : E ≃ₜ E) (hT : Differentiable ℝ T)
    (hdet : ∀ x, LinearMap.det (fderiv ℝ T x).toLinearMap = 1) : Measure.map T μ = μ := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar μ
    (s := Set.univ) (f' := fderiv ℝ T) nullMeasurableSet_univ
    (fun x _ => (hT x).hasFDerivAt.hasFDerivWithinAt) T.injective.injOn
  have hr : T '' Set.univ = Set.univ := by rw [image_univ, T.surjective.range_eq]
  simpa only [hdet, abs_one, ENNReal.ofReal_one, withDensity_const, one_smul,
    Measure.restrict_univ, hr] using h

end Hindman168
