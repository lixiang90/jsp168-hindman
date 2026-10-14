import Hindman168.NativeConjugateCanonicalProbability
import Hindman168.NativeBasepointObservable

/-! Actual original continuous observables pull back along the TRUE
right-coset isometry. Unit Lipschitz bounds and canonical Haar integral
are retained. Original LEFT translations keep genuine compact families,
without assuming those translations are uniformly spatially Lipschitz. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeConjugateRightObservable {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (ρ : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
    letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
      (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ,ℂ) → C(D.G ⧸ roughConjugateSubgroup D.Γ ρ,ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
  intro F
  exact F.comp ⟨roughConjugateRightCosetMap D.Γ ρ,
    (roughConjugateRightCosetIsometryEquiv D.Γ ρ).continuous⟩

theorem native_conjugate_right_observable_apply {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (ρ : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
    letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
      (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (q : D.G ⧸ roughConjugateSubgroup D.Γ ρ),
      nativeConjugateRightObservable D ρ F q=F (roughConjugateRightCosetMap D.Γ ρ q) := by intro F q; rfl

theorem native_conjugate_right_observable_continuous {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (ρ : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
    letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
      (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
    Continuous (nativeConjugateRightObservable D ρ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
  letI := native_nilmanifold_metric_quotient_compact D
  letI := native_nilmanifold_metric_quotient_compact (nativeConjugateNilmanifoldData D ρ)
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : C(D.G ⧸ D.Γ,ℂ) × (D.G ⧸ roughConjugateSubgroup D.Γ ρ) =>
    p.1 (roughConjugateRightCosetMap D.Γ ρ p.2))
  exact continuous_eval.comp (continuous_fst.prodMk
    ((roughConjugateRightCosetIsometryEquiv D.Γ ρ).continuous.comp continuous_snd))

theorem native_conjugate_right_observable_unit {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (ρ : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
    letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
      (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
    ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
      nativeConjugateRightObservable D ρ F ∈ unitLipschitzObservables (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
  intro F hF
  refine ⟨?_,fun q => hF.2 (roughConjugateRightCosetMap D.Γ ρ q)⟩
  apply LipschitzWith.mk_one
  intro x y
  change dist (F (roughConjugateRightCosetMap D.Γ ρ x)) (F (roughConjugateRightCosetMap D.Γ ρ y)) ≤
    dist (roughConjugateRightCosetMap D.Γ ρ x) (roughConjugateRightCosetMap D.Γ ρ y)
  simpa only [NNReal.coe_one,one_mul] using hF.1.dist_le_mul
    (roughConjugateRightCosetMap D.Γ ρ x) (roughConjugateRightCosetMap D.Γ ρ y)

theorem native_conjugate_right_observable_integral {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (ρ : D.G) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
    letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
      (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      (∫ q, nativeConjugateRightObservable D ρ F q
        ∂nativeNilmanifoldQuotientProbability (nativeConjugateNilmanifoldData D ρ))=
          ∫ q, F q ∂nativeNilmanifoldQuotientProbability D := by
  intro F
  exact native_conjugate_right_canonical_integral D ρ F

end Hindman168
