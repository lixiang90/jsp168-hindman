import Hindman168.NativeRationalCurveHaarImage
import Hindman168.FiniteProbabilityMixture

/-! Actual uniform mixture over rational residues of curve-averaged Haar images. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativePointMixtureMeasure {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (M : ℕ) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) :
    letI : MeasurableSpace D.G := borel D.G
    Measure (D.G ⧸ D.Γ) := by
  letI : MeasurableSpace D.G := borel D.G
  exact finiteProbabilityMixture (fun r => nativeRationalCurveHaarImage D H 0 (sigma r) (hRat r) h)

theorem native_point_mixture_isProbability {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hh : Continuous h) :
    letI : MeasurableSpace D.G := borel D.G
    IsProbabilityMeasure (nativePointMixtureMeasure D H M sigma hRat h) := by
  letI : MeasurableSpace D.G := borel D.G
  letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  exact finite_probability_mixture_isProbability _ (fun r =>
    native_rational_curve_haar_isProbability D H 0 (sigma r) (hRat r) h hh)

theorem native_point_mixture_integral {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (M : ℕ) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hh : Continuous h) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ J : C(D.G ⧸ D.Γ,ℂ),
      (∫ y, J y ∂nativePointMixtureMeasure D H M sigma hRat h) =
        finiteComplexMean (fun r : Fin M => ∫ beta in (0 : ℝ)..1,
          ∫ y, J y ∂nativeRationalLayerHaarImage D H 0 (sigma r) (hRat r) (h beta)) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro J
  have hInt (r : Fin M) : Integrable J (nativeRationalCurveHaarImage D H 0 (sigma r) (hRat r) h) := by
    letI := native_rational_curve_haar_isProbability D H 0 (sigma r) (hRat r) h hh
    exact (integrable_const ‖J‖).mono' J.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall J.norm_coe_le_norm)
  rw [nativePointMixtureMeasure, finite_probability_mixture_integral _ _ hInt]
  congr 1
  funext r
  exact native_rational_curve_haar_integral D H 0 (sigma r) (hRat r) h hh J

end Hindman168
