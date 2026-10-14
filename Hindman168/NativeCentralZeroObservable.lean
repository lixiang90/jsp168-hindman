import Hindman168.NativeCentralFactorTopology
import Hindman168.CentralFactorObservableDescent
import Hindman168.NativeCentralFourierCompactFamilies

/-! The ACTUAL zero vertical Fourier mode descends continuously to the
ACTUAL original central quotient/image lattice. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeCentralZeroObservable {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ, ℂ) → C(nativeCentralFactorSpace D, ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  exact (native_central_factor_metric_openQuotient D).isQuotientMap.lift
    (f := ⟨centralFactorCosetMap D.Γ, (native_central_factor_metric_openQuotient D).continuous⟩)
    (nativeCentralFourierProjection D 0 F) (by
      intro q r h
      obtain ⟨a, rfl⟩ := (native_central_factor_torus_fiber_iff D q r).mp h
      exact (native_central_fourier_projection_zero_invariant D F q a).symm)

theorem native_central_zero_observable_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : D.G ⧸ D.Γ),
      nativeCentralZeroObservable D F (centralFactorCosetMap D.Γ q) = nativeCentralFourierProjection D 0 F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F q
  have h := (native_central_factor_metric_openQuotient D).isQuotientMap.lift_comp
    (f := ⟨centralFactorCosetMap D.Γ, (native_central_factor_metric_openQuotient D).continuous⟩)
    (nativeCentralFourierProjection D 0 F) (by
      intro q r h
      obtain ⟨a, rfl⟩ := (native_central_factor_torus_fiber_iff D q r).mp h
      exact (native_central_fourier_projection_zero_invariant D F q a).symm)
  exact congrArg (fun K : C(D.G ⧸ D.Γ, ℂ) => K q) h

theorem native_central_zero_observable_unique {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (K : C(nativeCentralFactorSpace D, ℂ)),
      (∀ q, K (centralFactorCosetMap D.Γ q) = nativeCentralFourierProjection D 0 F q) →
        K = nativeCentralZeroObservable D F := by
  intro F K hK
  ext y
  obtain ⟨q, rfl⟩ := central_factor_coset_map_surjective D.Γ y
  rw [hK, native_central_zero_observable_apply]

theorem native_central_zero_observable_norm {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    letI : CompactSpace (nativeCentralFactorSpace D) := native_central_factor_compact D
    ∀ F : C(D.G ⧸ D.Γ, ℂ), ‖nativeCentralZeroObservable D F‖ ≤ ‖F‖ := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI : CompactSpace (nativeCentralFactorSpace D) := native_central_factor_compact D
  intro F
  apply (ContinuousMap.norm_le _ (norm_nonneg F)).mpr
  intro y
  obtain ⟨q, rfl⟩ := central_factor_coset_map_surjective D.Γ y
  rw [native_central_zero_observable_apply]
  exact ((nativeCentralFourierProjection D 0 F).norm_coe_le_norm q).trans
    (native_central_fourier_projection_norm D 0 F)

end Hindman168
