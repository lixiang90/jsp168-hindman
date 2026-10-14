import Hindman168.WeightedShearWeakLimit
import Hindman168.WeightedShearNativeTranslation
import Hindman168.NativeNilmanifoldProbabilityUniqueness
import Hindman168.NativeMetricCosetTranslation

/-!
The full weighted-box law on one native nilmanifold converges to its actual
canonical Haar probability. The data may be the native model of the joint
rational subgroup; no inference from marginal Haar laws is used.
-/
namespace Hindman168
open MeasureTheory Filter Module
open scoped Topology Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

/-- The actual exponential-coordinate projection to the original coset space. -/
noncomputable def weightedShearNativeProjection {s n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (b : Basis (Fin n) ℝ D.E) :
    (Fin n → ℝ) → D.G ⧸ D.Γ := fun x =>
  QuotientGroup.mk (nativeLieExponential (I := D.I) (G := D.G) (b.equivFun.symm x))

theorem weightedShearNativeProjection_continuous {s n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (b : Basis (Fin n) ℝ D.E) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (weightedShearNativeProjection D b) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact D.metric_quotientMap.continuous.comp
    ((nativeLieExponential_continuous (I := D.I) (G := D.G)).comp b.equivFunL.symm.continuous)

/-- The genuine projected box probability on the one complete homogeneous space. -/
noncomputable def weightedShearNativeBoxProbability {s n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (w : Fin n → ℕ) (b : Basis (Fin n) ℝ D.E) (E : ℝ) :
    letI : MeasurableSpace D.G := borel D.G
    ProbabilityMeasure (D.G ⧸ D.Γ) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  exact (weightedShearBoxProbability w E).map
    (weightedShearNativeProjection_continuous D b).measurable.aemeasurable

/-- The same actual quotient law after one fixed shear (including any fixed word). -/
noncomputable def weightedShearNativeShearedBoxProbability {s n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (w : Fin n → ℕ) (b : Basis (Fin n) ℝ D.E)
    (f : weightedShearGroup (R := ℝ) w) (E : ℝ) :
    letI : MeasurableSpace D.G := borel D.G
    ProbabilityMeasure (D.G ⧸ D.Γ) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  exact (weightedShearBoxProbability w E).map
    ((weightedShearNativeProjection_continuous D b).comp
      (weightedShearPoint_continuous f.val)).measurable.aemeasurable

/-- Lemma 7.7: actual weighted boxes converge weakly to the full native quotient Haar law. -/
theorem weightedShear_native_box_haar_tendsto {s n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (w : Fin n → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) (hwpos : ∀ i, 0 < w i)
    (F : ℕ → Submodule ℝ D.E) (hF : Antitone F) (hFone : F 1 = ⊤)
    (hB : ∀ i j v z, v ∈ F i → z ∈ F j →
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v z ∈ F (i+j))
    (b : Basis (Fin n) ℝ D.E) (hb : ∀ i, b i ∈ F (w i))
    (hcoord : ∀ i z, z ∈ F (w i+1) → b.coord i z = 0) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
    Tendsto (weightedShearNativeBoxProbability D w b) atTop
      (𝓝 (⟨nativeNilmanifoldQuotientProbability D,
        native_nilmanifold_quotient_probability_isProbability D⟩ : ProbabilityMeasure (D.G ⧸ D.Γ))) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  apply weightedShearBoxProbability_projection_tendsto w d hw hwpos
    (weightedShearNativeProjection D b) (weightedShearNativeProjection_continuous D b)
    _ (nativeMetricCosetTranslation D)
  · intro η hη
    apply ProbabilityMeasure.toMeasure_injective
    apply native_nilmanifold_invariant_probability_unique D η.toMeasure inferInstance
    intro g
    exact congrArg ProbabilityMeasure.toMeasure (hη g)
  · intro g
    have hv : nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g ∈ F 1 := by
      rw [hFone]
      exact Submodule.mem_top
    obtain ⟨f, hf⟩ := weightedShear_native_left_action D w F hF hB b hb hcoord hv
    refine ⟨f, ?_⟩
    intro x
    change QuotientGroup.mk (nativeLieExponential (I := D.I) (G := D.G)
      (b.equivFun.symm (f • x))) = g • weightedShearNativeProjection D b x
    rw [hf, LinearEquiv.symm_apply_apply, nativeLieExponential_globalLogarithm,
      nativeLieExponential_globalLogarithm]
    rfl

/-- Every fixed shear, and hence every fixed product of lifts, has the same full Haar limit. -/
theorem weightedShear_native_sheared_box_haar_tendsto {s n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (w : Fin n → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) (hwpos : ∀ i, 0 < w i)
    (F : ℕ → Submodule ℝ D.E) (hF : Antitone F) (hFone : F 1 = ⊤)
    (hB : ∀ i j v z, v ∈ F i → z ∈ F j →
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v z ∈ F (i+j))
    (b : Basis (Fin n) ℝ D.E) (hb : ∀ i, b i ∈ F (w i))
    (hcoord : ∀ i z, z ∈ F (w i+1) → b.coord i z = 0)
    (f : weightedShearGroup (R := ℝ) w) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
    Tendsto (weightedShearNativeShearedBoxProbability D w b f) atTop
      (𝓝 (⟨nativeNilmanifoldQuotientProbability D,
        native_nilmanifold_quotient_probability_isProbability D⟩ : ProbabilityMeasure (D.G ⧸ D.Γ))) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  exact weightedShearBoxProbability_shear_projection_tendsto w d hw hwpos
    (weightedShearNativeProjection D b) (weightedShearNativeProjection_continuous D b) _ f
    (weightedShear_native_box_haar_tendsto D w d hw hwpos F hF hFone hB b hb hcoord)

end Hindman168
