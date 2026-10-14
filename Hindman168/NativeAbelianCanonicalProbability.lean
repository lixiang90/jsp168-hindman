import Hindman168.NativeNilmanifoldQuotientProbability
import Hindman168.NativeAbelianTorusHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace Hindman168
open MeasureTheory Measure Set
open scoped Classical Manifold ContDiff
universe u

/-- The actual general nonnormal quotient construction has EXACT product
Haar coordinates in the abelian case. No measure agreement is assumed. -/
theorem native_abelian_quotient_probability_coordinates (D : NativeNilmanifoldData.{u} 1) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Measure.map (nativeAbelianMetricTorusHomeomorph D) (nativeNilmanifoldQuotientProbability D) =
      Measure.pi (fun _ : ↥(nativeFilteredHorizontalIndices (I := D.I) D.Γ) => AddCircle.haarAddCircle) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  let e := nativeAbelianMetricTorusHomeomorph D
  let T := UnitAddTorus ↥(nativeFilteredHorizontalIndices (I := D.I) D.Γ)
  let μ := nativeNilmanifoldQuotientProbability D
  let ν : Measure T := Measure.map e μ
  let H : Measure T := Measure.pi (fun _ : ↥(nativeFilteredHorizontalIndices (I := D.I) D.Γ) => AddCircle.haarAddCircle)
  letI : IsProbabilityMeasure μ := native_nilmanifold_quotient_probability_isProbability D
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  have hν : ∀ a : T, Measure.map (fun x : T => a+x) ν = ν := by
    intro a
    obtain ⟨g, hg⟩ := native_horizontal_torus_projection_surjective (I := D.I) D.Γ a
    have ha : Measurable (fun x : T => a+x) := (Homeomorph.addLeft a).measurable
    have he : (fun x : T => a+x) ∘ e = e ∘ (fun q : D.G ⧸ D.Γ => g • q) := by
      funext q
      change a+e q = e (g • q)
      rw [← hg]
      exact (native_abelian_metric_torus_action D g q).symm
    have hact : (fun q : D.G ⧸ D.Γ => g • q) = e.symm ∘ (fun x : T => a+x) ∘ e := by
      funext q
      apply e.injective
      change e (g • q) = e (e.symm (a+e q))
      rw [Homeomorph.apply_symm_apply]
      exact (congrFun he q).symm
    have hmeas : Measurable (fun q : D.G ⧸ D.Γ => g • q) := by
      rw [hact]
      exact e.symm.measurable.comp (ha.comp e.measurable)
    change Measure.map _ (Measure.map e μ) = Measure.map e μ
    rw [Measure.map_map ha e.measurable, he, ← Measure.map_map e.measurable hmeas,
      native_nilmanifold_quotient_probability_translate]
  letI : IsAddLeftInvariant ν := ⟨hν⟩
  letI : IsAddLeftInvariant H := inferInstance
  letI : IsProbabilityMeasure H := inferInstance
  letI : IsAddHaarMeasure ν := isAddHaarMeasure_of_isCompact_nonempty_interior ν Set.univ
    isCompact_univ (by simp only [interior_univ]; exact univ_nonempty)
    (by simp only [measure_univ]; norm_num) (by simp only [measure_univ]; norm_num)
  letI : IsAddHaarMeasure H := isAddHaarMeasure_of_isCompact_nonempty_interior H Set.univ
    isCompact_univ (by simp only [interior_univ]; exact univ_nonempty)
    (by simp only [measure_univ]; norm_num) (by simp only [measure_univ]; norm_num)
  exact isAddHaarMeasure_eq_of_isProbabilityMeasure ν H

theorem native_abelian_quotient_probability_integral (D : NativeNilmanifoldData.{u} 1) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ), (∫ q, F q ∂nativeNilmanifoldQuotientProbability D) =
      ∫ x, F ((nativeAbelianMetricTorusHomeomorph D).symm x)
        ∂Measure.pi (fun _ : ↥(nativeFilteredHorizontalIndices (I := D.I) D.Γ) => AddCircle.haarAddCircle) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  intro F
  rw [← native_abelian_quotient_probability_coordinates D]
  rw [(nativeAbelianMetricTorusHomeomorph D).measurableEmbedding.integral_map]
  simp only [Homeomorph.symm_apply_apply]

end Hindman168
