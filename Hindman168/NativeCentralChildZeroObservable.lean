import Hindman168.NativeCentralCanonicalDiscrepancy

/-! SAME actual descended zero observable in the CHILD's actual specified
compatible metric, with genuine compact uniform-function family. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeCentralChildZeroObservable {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeCentralQuotientData D).metric
    letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
      (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ, ℂ) → C((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ, ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeCentralQuotientData D).metric
  letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
  intro F
  refine ⟨nativeCentralZeroObservable D F, ?_⟩
  exact Eq.mp (congrArg (fun t : TopologicalSpace (nativeCentralFactorSpace D) =>
    @Continuous (nativeCentralFactorSpace D) ℂ t inferInstance (nativeCentralZeroObservable D F))
      (nativeNilmanifold_metric_topology (nativeCentralQuotientData D)))
        (nativeCentralZeroObservable D F).continuous

theorem native_central_child_zero_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : D.G ⧸ D.Γ),
      nativeCentralChildZeroObservable D F (centralFactorCosetMap D.Γ q) = nativeCentralFourierProjection D 0 F q := by
  intro F q
  exact native_central_zero_observable_apply D F q

theorem native_central_child_zero_sub {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeCentralQuotientData D).metric
    letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
      (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
    ∀ F G : C(D.G ⧸ D.Γ, ℂ), nativeCentralChildZeroObservable D (F-G) =
      nativeCentralChildZeroObservable D F - nativeCentralChildZeroObservable D G := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeCentralQuotientData D).metric
  letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
  intro F G
  ext y
  change nativeCentralZeroObservable D (F-G) y =
    nativeCentralZeroObservable D F y - nativeCentralZeroObservable D G y
  have h := native_central_zero_observable_sub D F G
  simpa only [ContinuousMap.sub_apply] using congrArg (fun K => K y) h

theorem native_central_child_zero_norm {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    letI := (nativeCentralQuotientData D).metric
    letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
      (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
      native_nilmanifold_metric_quotient_compact (nativeCentralQuotientData D)
    ∀ F : C(D.G ⧸ D.Γ, ℂ), ‖nativeCentralChildZeroObservable D F‖ ≤ ‖F‖ := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI := (nativeCentralQuotientData D).metric
  letI : TopologicalSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    (nativeCentralQuotientData D).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace ((nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeCentralQuotientData D)
  intro F
  apply (ContinuousMap.norm_le _ (norm_nonneg F)).mpr
  intro y
  obtain ⟨q, rfl⟩ := central_factor_coset_map_surjective D.Γ y
  rw [native_central_child_zero_apply]
  exact ((nativeCentralFourierProjection D 0 F).norm_coe_le_norm q).trans
    (native_central_fourier_projection_norm D 0 F)

end Hindman168
