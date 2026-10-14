import Hindman168.NativeCentralFourierCompactFamilies

/-! Exact finite sampling minus the constructed original quotient Haar mean. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff Classical
universe u

noncomputable def nativeNilmanifoldFiniteDiscrepancy {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    {α : Type*} (a : Finset α) (f : α → D.G ⧸ D.Γ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ, ℂ) →ₗ[ℂ] ℂ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact {
    toFun := fun F => finiteComplexSetMean a (fun x => F (f x)) -
      ∫ q, F q ∂nativeNilmanifoldQuotientProbability D
    map_add' := fun F G => by
      simp only [ContinuousMap.add_apply, finiteComplexSetMean, Finset.sum_add_distrib, add_div,
        integral_add (native_nilmanifold_probability_integrable D F)
          (native_nilmanifold_probability_integrable D G)]
      ring
    map_smul' := fun c F => by
      simp only [ContinuousMap.smul_apply, finiteComplexSetMean, ← Finset.smul_sum,
        smul_div_assoc, integral_smul, smul_sub, RingHom.id_apply] }

theorem native_nilmanifold_finite_discrepancy_norm {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    {α : Type*} (a : Finset α) (f : α → D.G ⧸ D.Γ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    ∀ F : C(D.G ⧸ D.Γ, ℂ), ‖nativeNilmanifoldFiniteDiscrepancy D a f F‖ ≤ 2*‖F‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro F
  have hm := finiteComplexSetMean_norm_bound a (fun x => F (f x)) ‖F‖ (norm_nonneg F)
    (fun x _ => F.norm_coe_le_norm _)
  have hi := native_nilmanifold_probability_integral_bound D F ‖F‖ F.norm_coe_le_norm
  exact (norm_sub_le _ _).trans (by linarith only [hm, hi])

theorem native_nilmanifold_finite_discrepancy_nonzero_projection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) {α : Type*} (a : Finset α) (f : α → D.G ⧸ D.Γ)
    (k : nativeNilmanifoldCenterIndex D → ℤ) (hk : k ≠ 0) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      nativeNilmanifoldFiniteDiscrepancy D a f (nativeCentralFourierProjection D k F) =
        finiteComplexSetMean a (fun x => nativeCentralFourierProjection D k F (f x)) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  change _ - ∫ q, nativeCentralFourierProjection D k F q ∂nativeNilmanifoldQuotientProbability D = _
  rw [native_central_fourier_projection_nonzero_mean D k hk, sub_zero]

end Hindman168
