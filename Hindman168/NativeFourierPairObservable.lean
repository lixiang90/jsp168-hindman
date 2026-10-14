import Hindman168.ContinuousConjugatePair
import Hindman168.NativeCentralFourierCompactFamilies
import Hindman168.DiagonalCenterSubgroup

/-! ACTUAL paired Fourier observable on original product lattice cosets.
The metric/raw topology comparison is proved, not asserted definitional. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeProductMetricProjection {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C((D.G × D.G) ⧸ D.Γ.prod D.Γ, (D.G ⧸ D.Γ) × (D.G ⧸ D.Γ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  refine ⟨productCosetMap D.Γ D.Γ, ?_⟩
  have hm : @Continuous ((D.G × D.G) ⧸ D.Γ.prod D.Γ) ((D.G ⧸ D.Γ) × (D.G ⧸ D.Γ))
      (productCosetMetric D.Γ D.Γ).toUniformSpace.toTopologicalSpace inferInstance
        (productCosetMap D.Γ D.Γ) := by
    letI := productCosetMetric D.Γ D.Γ
    exact (productCosetIsometryEquiv D.Γ D.Γ).continuous
  exact Eq.mp (congrArg (fun t : TopologicalSpace ((D.G × D.G) ⧸ D.Γ.prod D.Γ) =>
    @Continuous ((D.G × D.G) ⧸ D.Γ.prod D.Γ) ((D.G ⧸ D.Γ) × (D.G ⧸ D.Γ))
      t inferInstance (productCosetMap D.Γ D.Γ))
        (productCosetMetric_topology_eq D.Γ D.Γ D.metric_quotientMap D.metric_quotientMap))
    hm

noncomputable def nativeFourierPairObservable {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ, ℂ) → C((D.G × D.G) ⧸ D.Γ.prod D.Γ, ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  exact (continuousConjugatePair (nativeCentralFourierProjection D k F)
    (nativeCentralFourierProjection D k F)).comp (nativeProductMetricProjection D)

theorem native_fourier_pair_observable_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : (D.G × D.G) ⧸ D.Γ.prod D.Γ),
      nativeFourierPairObservable D k F q =
        nativeCentralFourierProjection D k F (productCosetMap D.Γ D.Γ q).1 *
          star (nativeCentralFourierProjection D k F (productCosetMap D.Γ D.Γ q).2) := by
  intro F q
  rfl

theorem native_fourier_pair_observable_continuous {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (nativeFourierPairObservable D k) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hp := (native_central_fourier_projection_functionspace_lipschitz D k).continuous
  have h1 : Continuous (fun p : C(D.G ⧸ D.Γ, ℂ) × ((D.G × D.G) ⧸ D.Γ.prod D.Γ) =>
      nativeCentralFourierProjection D k p.1 (nativeProductMetricProjection D p.2).1) :=
    continuous_eval.comp ((hp.comp continuous_fst).prodMk
      (((nativeProductMetricProjection D).continuous.comp continuous_snd).fst))
  have h2 : Continuous (fun p : C(D.G ⧸ D.Γ, ℂ) × ((D.G × D.G) ⧸ D.Γ.prod D.Γ) =>
      nativeCentralFourierProjection D k p.1 (nativeProductMetricProjection D p.2).2) :=
    continuous_eval.comp ((hp.comp continuous_fst).prodMk
      (((nativeProductMetricProjection D).continuous.comp continuous_snd).snd))
  exact h1.mul h2.star

theorem native_fourier_pair_family_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact (nativeFourierPairObservable D k '' unitLipschitzObservables (D.G ⧸ D.Γ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact (unit_lipschitz_observables_compact (D.G ⧸ D.Γ)).image (native_fourier_pair_observable_continuous D k)

end Hindman168
