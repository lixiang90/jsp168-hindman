import Hindman168.NativeAbelianTorusHaar
import Hindman168.NativeNilmanifoldBorelProbability

/-! Actual torus-coordinate Haar equals the genuine original canonical
probability after explicit PROVED sigma-algebra transport. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_abelian_torus_haar_canonical (D : NativeNilmanifoldData.{u} 1) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    measurableSpaceMeasureTransport
      (congrArg (fun t : TopologicalSpace (D.G ⧸ D.Γ) => @borel (D.G ⧸ D.Γ) t)
        (nativeNilmanifold_metric_topology D)).symm (nativeAbelianTorusHaar D) =
      nativeNilmanifoldBorelProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  let h := congrArg (fun t : TopologicalSpace (D.G ⧸ D.Γ) => @borel (D.G ⧸ D.Γ) t)
    (nativeNilmanifold_metric_topology D)
  let ν := measurableSpaceMeasureTransport h.symm (nativeAbelianTorusHaar D)
  have hp : IsProbabilityMeasure ν := measurable_space_measure_transport_probability h.symm _
    (native_abelian_torus_haar_probability D)
  have hi : ∀ g : D.G, Measure.map (fun q : D.G ⧸ D.Γ => g • q) ν = ν := by
    intro g
    change Measure.map _ (measurableSpaceMeasureTransport h.symm _) = _
    rw [← measurable_space_measure_transport_map h.symm,
      native_abelian_torus_haar_translation_invariant]
  exact native_nilmanifold_borel_probability_unique D ν hp hi

theorem native_abelian_torus_haar_canonical_integral (D : NativeNilmanifoldData.{u} 1) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    ∀ f : (D.G ⧸ D.Γ) → ℂ,
      (letI := D.metric;
        letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace;
        letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ);
        ∫ q, f q ∂nativeAbelianTorusHaar D) =
      ∫ q, f q ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  intro f
  let h := congrArg (fun t : TopologicalSpace (D.G ⧸ D.Γ) => @borel (D.G ⧸ D.Γ) t)
    (nativeNilmanifold_metric_topology D)
  have ht := measurable_space_measure_transport_integral h.symm (nativeAbelianTorusHaar D) f
  rw [native_abelian_torus_haar_canonical] at ht
  exact ht.symm.trans (native_nilmanifold_borel_probability_integral D f)

end Hindman168
