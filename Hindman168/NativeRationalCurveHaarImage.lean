import Hindman168.NativeRationalLayerOrbitObservables
import Hindman168.UnitIntervalProbability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The actual measure obtained by averaging one original subgroup Haar
image along a continuous curve over the unit interval. Constructed as a
product-probability pushforward, without assuming a measure-valued integral. -/
namespace Hindman168
open MeasureTheory Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalCurveHaarImage {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) :
    letI : MeasurableSpace D.G := borel D.G
    Measure (D.G ⧸ D.Γ) := by
  letI : MeasurableSpace D.G := borel D.G
  let A := nativeRationalLayerOrbitData D F i rho hRat
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  exact Measure.map (fun z : ℝ × (A.G ⧸ A.Γ) => nativeRationalLayerOrbitMap D F i rho hRat (h z.1) z.2)
    (unitIntervalProbability.prod (nativeNilmanifoldQuotientProbability A))

theorem native_rational_curve_haar_isProbability {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hh : Continuous h) :
    letI : MeasurableSpace D.G := borel D.G
    IsProbabilityMeasure (nativeRationalCurveHaarImage D F i rho hRat h) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  let A := nativeRationalLayerOrbitData D F i rho hRat
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_metric_coset_borel A
  letI := unit_interval_probability_isProbability
  letI := native_nilmanifold_quotient_probability_isProbability A
  have hc : Continuous (fun z : ℝ × (A.G ⧸ A.Γ) => nativeRationalLayerOrbitMap D F i rho hRat (h z.1) z.2) :=
    (native_rational_layer_orbit_metric_joint_continuous D F i rho hRat).comp
      ((hh.comp continuous_fst).prodMk continuous_snd)
  exact Measure.isProbabilityMeasure_map hc.measurable.aemeasurable

theorem native_rational_curve_haar_integral {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hh : Continuous h) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ J : C(D.G ⧸ D.Γ,ℂ),
      (∫ y, J y ∂nativeRationalCurveHaarImage D F i rho hRat h) =
        ∫ beta in (0 : ℝ)..1, ∫ y, J y ∂nativeRationalLayerHaarImage D F i rho hRat (h beta) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  let A := nativeRationalLayerOrbitData D F i rho hRat
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_metric_coset_borel A
  letI := unit_interval_probability_isProbability
  letI := native_nilmanifold_quotient_probability_isProbability A
  intro J
  let T : ℝ × (A.G ⧸ A.Γ) → D.G ⧸ D.Γ :=
    fun z => nativeRationalLayerOrbitMap D F i rho hRat (h z.1) z.2
  have hT : Continuous T := (native_rational_layer_orbit_metric_joint_continuous D F i rho hRat).comp
    ((hh.comp continuous_fst).prodMk continuous_snd)
  have hInt : Integrable (fun z => J (T z)) (unitIntervalProbability.prod (nativeNilmanifoldQuotientProbability A)) :=
    (integrable_const ‖J‖).mono' (J.continuous.comp hT).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => J.norm_coe_le_norm (T z)))
  change (∫ y, J y ∂Measure.map T (unitIntervalProbability.prod (nativeNilmanifoldQuotientProbability A))) = _
  rw [integral_map hT.measurable.aemeasurable J.continuous.aestronglyMeasurable,
    integral_prod _ hInt, intervalIntegral.integral_of_le zero_le_one]
  change (∫ beta in Ioc (0 : ℝ) 1, ∫ x, J (T (beta,x)) ∂nativeNilmanifoldQuotientProbability A) = _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun beta =>
    (native_rational_layer_haar_image_integral D F i rho hRat (h beta) J).symm)

end Hindman168
