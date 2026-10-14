import Hindman168.NativeCentralZeroCompactFamilies
import Mathlib.MeasureTheory.Group.Measure

/-! Actual probability on the original central factor by original quotient
pushforward, with exact integrals. Equality to a separately built Haar awaits proof. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeCentralFactorProbability {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
    Measure (nativeCentralFactorSpace D) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
  exact Measure.map (centralFactorCosetMap D.Γ) (nativeNilmanifoldQuotientProbability D)

theorem native_central_factor_probability_isProbability {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
    IsProbabilityMeasure (nativeCentralFactorProbability D) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
  letI : BorelSpace (nativeCentralFactorSpace D) := ⟨rfl⟩
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  letI := native_nilmanifold_quotient_probability_isProbability D
  exact Measure.isProbabilityMeasure_map (native_central_factor_metric_openQuotient D).continuous.measurable.aemeasurable

theorem native_central_factor_probability_integral {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
    ∀ F : C(nativeCentralFactorSpace D, ℂ),
      (∫ y, F y ∂nativeCentralFactorProbability D) =
        ∫ q, F (centralFactorCosetMap D.Γ q) ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
  letI : BorelSpace (nativeCentralFactorSpace D) := ⟨rfl⟩
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  intro F
  exact integral_map (native_central_factor_metric_openQuotient D).continuous.measurable.aemeasurable
    F.continuous.aestronglyMeasurable

theorem native_central_factor_zero_integral {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ), (∫ y, nativeCentralZeroObservable D F y ∂nativeCentralFactorProbability D) =
      ∫ q, nativeCentralFourierProjection D 0 F q ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [native_central_factor_probability_integral]
  simp only [native_central_zero_observable_apply]

theorem native_central_factor_probability_translate {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (h : D.G ⧸ Subgroup.center D.G) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
    Measure.map (fun y : nativeCentralFactorSpace D => h • y) (nativeCentralFactorProbability D) =
      nativeCentralFactorProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeCentralFactorSpace D) := borel (nativeCentralFactorSpace D)
  letI : BorelSpace (nativeCentralFactorSpace D) := ⟨rfl⟩
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
  have hg : Measurable (fun q : D.G ⧸ D.Γ => g • q) := (continuous_const_smul g).measurable
  have hb : Measurable (fun y : nativeCentralFactorSpace D => (g : D.G ⧸ Subgroup.center D.G) • y) :=
    (continuous_const_smul (g : D.G ⧸ Subgroup.center D.G)).measurable
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  have hp := (native_central_factor_metric_openQuotient D).continuous.measurable
  have he : (fun y : nativeCentralFactorSpace D => (g : D.G ⧸ Subgroup.center D.G) • y) ∘
      centralFactorCosetMap D.Γ = centralFactorCosetMap D.Γ ∘ (fun q : D.G ⧸ D.Γ => g • q) := by
    funext q
    exact (central_factor_coset_map_equivariant D.Γ g q).symm
  change Measure.map _ (Measure.map _ _) = Measure.map _ _
  rw [Measure.map_map hb hp, he, ← Measure.map_map hp hg,
    native_nilmanifold_quotient_probability_translate]

end Hindman168
