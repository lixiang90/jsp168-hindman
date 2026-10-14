import Hindman168.ContinuousMapTopologyTransport
import Hindman168.NativeDiagonalCanonicalDiscrepancy
import Hindman168.NativeFourierPairFactorCompact

/-! SAME actual pair observable in genuine diagonal native specified metric.
Its uniform functionspace compactness is preserved, not spatial Lipschitzness. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] diagonal_center_normal

noncomputable def nativeDiagonalPairMetricObservable {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeDiagonalQuotientData D).metric
    letI : TopologicalSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
      (nativeDiagonalQuotientData D).metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ, ℂ) → C((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ, ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeDiagonalQuotientData D).metric
  letI : TopologicalSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
    (nativeDiagonalQuotientData D).metric.toUniformSpace.toTopologicalSpace
  intro F
  exact continuousMapTopologyTransport (nativeDiagonalFactorSpace D)
    (QuotientGroup.instTopologicalSpace ((D.Γ.prod D.Γ).map (QuotientGroup.mk' (diagonalCenterSubgroup D.G))))
    (nativeDiagonalQuotientData D).metric.toUniformSpace.toTopologicalSpace
    (nativeNilmanifold_metric_topology (nativeDiagonalQuotientData D)) (nativeFourierPairFactor D k F)

theorem native_diagonal_pair_metric_observable_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (y : nativeDiagonalFactorSpace D),
      nativeDiagonalPairMetricObservable D k F y = nativeFourierPairFactor D k F y := by
  intro F y
  exact continuous_map_topology_transport_apply (nativeDiagonalFactorSpace D) _ _ _ _ y

theorem native_diagonal_pair_metric_observable_continuous {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeDiagonalQuotientData D).metric
    letI : TopologicalSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
      (nativeDiagonalQuotientData D).metric.toUniformSpace.toTopologicalSpace
    Continuous (nativeDiagonalPairMetricObservable D k) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeDiagonalQuotientData D).metric
  letI : TopologicalSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
    (nativeDiagonalQuotientData D).metric.toUniformSpace.toTopologicalSpace
  exact (continuous_map_topology_transport_continuous (nativeDiagonalFactorSpace D) _ _
    (nativeNilmanifold_metric_topology (nativeDiagonalQuotientData D))).comp
      (native_fourier_pair_factor_continuous D k)

theorem native_diagonal_pair_metric_family_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeDiagonalQuotientData D).metric
    letI : TopologicalSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
      (nativeDiagonalQuotientData D).metric.toUniformSpace.toTopologicalSpace
    IsCompact (nativeDiagonalPairMetricObservable D k '' unitLipschitzObservables (D.G ⧸ D.Γ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeDiagonalQuotientData D).metric
  letI : TopologicalSpace ((nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) :=
    (nativeDiagonalQuotientData D).metric.toUniformSpace.toTopologicalSpace
  exact (unit_lipschitz_observables_compact (D.G ⧸ D.Γ)).image (native_diagonal_pair_metric_observable_continuous D k)

end Hindman168
