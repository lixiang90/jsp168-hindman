import Hindman168.PositivePrincipalSumMassDeduction
import Hindman168.WeightedShearJointOrbitHaar

/-! The finite closed-cover bound on the actual original joint coset.
The common Haar limit is supplied by the proved native weighted-box theorem. -/
namespace Hindman168
open MeasureTheory Filter Module
open scoped Topology Manifold ContDiff BigOperators ENNReal NNReal
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem principal_original_joint_haar_closed_cover {s ℓ n : ℕ} {O : Type*}
    [Fintype O] [Nonempty O]
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (b : Basis (Fin n) ℝ (nativeRationalLayerOrbitData D F 1 ρ hρ).E) (w : Fin n → ℕ)
    (hw : ∀ i, 1 ≤ w i ∧ w i ≤ ℓ ∧
      b i ∈ affineShearNativeInitialFiltration D F ρ hρ (w i) ∧
      affineShearNativeInitialFiltration D F ρ hρ (w i+1) ≤ (b.coord i).ker)
    (h : D.G) (f : O → weightedShearGroup (R := ℝ) w) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
    ∀ C : O → Set (D.G ⧸ D.Γ), (∀ o, IsClosed (C o)) →
      (∀ z : Fin n → ℝ, ∃ o, nativeRationalLayerOrbitMap D F 1 ρ hρ h
        (weightedShearNativeProjection (nativeRationalLayerOrbitData D F 1 ρ hρ) b (f o • z)) ∈ C o) →
      ((1 / (Fintype.card O : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ≤
        nativeRationalLayerHaarImage D F 1 ρ hρ h (⋃ o, C o) := by
  let A := nativeRationalLayerOrbitData D F 1 ρ hρ
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_metric_coset_borel A
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  intro C hC hcover
  let Y := fun o (z : Fin n → ℝ) => nativeRationalLayerOrbitMap D F 1 ρ hρ h
    (weightedShearNativeProjection A b (f o • z))
  have hY (o) : Continuous (Y o) :=
    (weightedShear_joint_orbit_map_continuous D F ρ hρ h).comp
      ((weightedShearNativeProjection_continuous A b).comp (weightedShearPoint_continuous (f o).val))
  let μ : ProbabilityMeasure (D.G ⧸ D.Γ) :=
    ⟨nativeRationalLayerHaarImage D F 1 ρ hρ h,
      native_rational_layer_haar_image_isProbability D F 1 ρ hρ h⟩
  have heq (o : O) (E : ℝ) (hE : 1 ≤ E) :
      weightedShearJointOrbitBoxProbability D F ρ hρ b w h (f o) E =
        (weightedShearBoxProbability w E).map (hY o).measurable.aemeasurable := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [weightedShearJointOrbitBoxProbability_actual_law D F ρ hρ b w h (f o) E hE,
      ProbabilityMeasure.toMeasure_map, weightedShearBoxProbability_actual_law w E hE]
  have hmass : ∀ᶠ E : ℝ in atTop, (1 : ℝ≥0) ≤
      ∑ o, weightedShearJointOrbitBoxProbability D F ρ hρ b w h (f o) E (C o) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with E hE
    have hp := principal_pointwise_cover_mass (weightedShearBoxProbability w E) Y
      (fun o => (hY o).measurable) C (fun o => (hC o).measurableSet) hcover
    simpa only [← heq _ E hE] using hp
  have hu := principal_same_limit_closed_union atTop
    (fun o => weightedShearJointOrbitBoxProbability D F ρ hρ b w h (f o)) μ C hC
    (fun o => weightedShear_joint_orbit_haar_tendsto_of_adapted_basis D F ρ hρ b w hw h (f o)) hmass
  simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, μ, ProbabilityMeasure.coe_mk] using (ENNReal.coe_le_coe.mpr hu)

end Hindman168
