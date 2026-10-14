import Hindman168.NativeRationalLayerOrbitObservables
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Continuity of the actual original Haar-image expectations. The measure
is transported from the SAME subgroup quotient; no empirical law is assumed. -/
namespace Hindman168
open MeasureTheory Set
open scoped Manifold ContDiff Topology
universe u v
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_layer_haar_integral_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    {T : Type v} [TopologicalSpace T] [FirstCountableTopology T] [LocallyCompactSpace T]
    (h : T → D.G) (hh : Continuous h) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ f : C(D.G ⧸ D.Γ,ℂ),
      Continuous (fun t => ∫ y, f y ∂nativeRationalLayerHaarImage D F i rho hRat (h t)) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro f
  let A := nativeRationalLayerOrbitData D F i rho hRat
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (A.G ⧸ A.Γ) := native_nilmanifold_metric_quotient_compact A
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_metric_coset_borel A
  letI := native_nilmanifold_quotient_probability_isProbability A
  have hj : Continuous (fun z : T × (A.G ⧸ A.Γ) =>
      f (nativeRationalLayerOrbitMap D F i rho hRat (h z.1) z.2)) :=
    f.continuous.comp ((native_rational_layer_orbit_metric_joint_continuous D F i rho hRat).comp
      ((hh.comp continuous_fst).prodMk continuous_snd))
  have hc := continuous_parametric_integral_of_continuous
    (μ := nativeNilmanifoldQuotientProbability A)
    (f := fun t x => f (nativeRationalLayerOrbitMap D F i rho hRat (h t) x))
    hj (s := univ) isCompact_univ
  have he : (fun t => ∫ y, f y ∂nativeRationalLayerHaarImage D F i rho hRat (h t)) =
      (fun t => ∫ x, f (nativeRationalLayerOrbitMap D F i rho hRat (h t) x)
        ∂nativeNilmanifoldQuotientProbability A) := by
    funext t
    exact native_rational_layer_haar_image_integral D F i rho hRat (h t) f
  rw [he]
  simpa only [Measure.restrict_univ] using hc

end Hindman168
