import Hindman168.NativeAbelianMetricTorus
import Hindman168.UnitTorusFiniteDiscrepancy

/-! Explicit normalized measure on the original abelian metric quotient.
It is the inverse-homeomorphism pushforward of product circle Haar. -/

namespace Hindman168
open MeasureTheory
open scoped Classical BigOperators Manifold ContDiff Topology
universe u

noncomputable def nativeAbelianTorusHaar (D : NativeNilmanifoldData.{u} 1) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
    Measure (D.G ⧸ D.Γ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  letI : BorelSpace (D.G ⧸ D.Γ) := ⟨rfl⟩
  exact Measure.map (nativeAbelianMetricTorusHomeomorph D).symm
    (Measure.pi (fun _ : ↥(nativeFilteredHorizontalIndices (I := D.I) D.Γ) => AddCircle.haarAddCircle))

theorem native_abelian_torus_haar_probability (D : NativeNilmanifoldData.{u} 1) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
    IsProbabilityMeasure (nativeAbelianTorusHaar D) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  letI : BorelSpace (D.G ⧸ D.Γ) := ⟨rfl⟩
  exact Measure.isProbabilityMeasure_map (nativeAbelianMetricTorusHomeomorph D).symm.measurable.aemeasurable

theorem native_abelian_torus_haar_coordinate_map (D : NativeNilmanifoldData.{u} 1) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
    Measure.map (nativeAbelianMetricTorusHomeomorph D) (nativeAbelianTorusHaar D) =
      Measure.pi (fun _ : ↥(nativeFilteredHorizontalIndices (I := D.I) D.Γ) => AddCircle.haarAddCircle) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  letI : BorelSpace (D.G ⧸ D.Γ) := ⟨rfl⟩
  exact (nativeAbelianMetricTorusHomeomorph D).toMeasurableEquiv.map_map_symm

theorem native_abelian_torus_haar_integral (D : NativeNilmanifoldData.{u} 1) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      (∫ q, F q ∂nativeAbelianTorusHaar D) =
        ∫ x, F ((nativeAbelianMetricTorusHomeomorph D).symm x)
          ∂Measure.pi (fun _ : ↥(nativeFilteredHorizontalIndices (I := D.I) D.Γ) => AddCircle.haarAddCircle) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  letI : BorelSpace (D.G ⧸ D.Γ) := ⟨rfl⟩
  intro F
  exact (nativeAbelianMetricTorusHomeomorph D).symm.measurableEmbedding.integral_map F

theorem native_abelian_metric_torus_action (D : NativeNilmanifoldData.{u} 1) (g : D.G) (q : D.G ⧸ D.Γ) :
    nativeAbelianMetricTorusHomeomorph D (g • q) =
      nativeHorizontalTorusProjection (I := D.I) D.Γ g + nativeAbelianMetricTorusHomeomorph D q := by
  induction q using Quotient.inductionOn with
  | _ h =>
    change nativeAbelianMetricTorusHomeomorph D (g*h : D.G ⧸ D.Γ) = _
    rw [native_abelian_metric_torus_homeomorph_mk, native_horizontal_torus_projection_mul,
      native_abelian_metric_torus_homeomorph_mk]

theorem native_abelian_torus_haar_translation_invariant (D : NativeNilmanifoldData.{u} 1) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
    Measure.map (fun q : D.G ⧸ D.Γ => g • q) (nativeAbelianTorusHaar D) = nativeAbelianTorusHaar D := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (D.G ⧸ D.Γ) := borel (D.G ⧸ D.Γ)
  letI : BorelSpace (D.G ⧸ D.Γ) := ⟨rfl⟩
  let e := nativeAbelianMetricTorusHomeomorph D
  let a := nativeHorizontalTorusProjection (I := D.I) D.Γ g
  have hact : (fun q : D.G ⧸ D.Γ => g • q) = fun q => e.symm (a+e q) := by
    funext q
    apply e.injective
    rw [Homeomorph.apply_symm_apply]
    exact native_abelian_metric_torus_action D g q
  have hm : Measurable (fun q : D.G ⧸ D.Γ => g • q) := by
    rw [hact]
    exact e.symm.measurable.comp ((measurable_const.add e.measurable))
  change Measure.map _ (Measure.map e.symm _) = Measure.map e.symm _
  rw [Measure.map_map hm e.symm.measurable]
  have he : ((fun q : D.G ⧸ D.Γ => g • q) ∘ e.symm) = e.symm ∘ (fun x => a+x) := by
    funext x
    simp only [Function.comp_apply, hact, Homeomorph.apply_symm_apply]
  have ha : Measurable (fun x : UnitAddTorus ↥(nativeFilteredHorizontalIndices (I := D.I) D.Γ) => a+x) :=
    (Homeomorph.addLeft a).measurable
  rw [he, ← Measure.map_map e.symm.measurable ha]
  rw [map_add_left_eq_self]

end Hindman168
