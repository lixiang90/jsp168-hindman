import Hindman168.NativeNilmanifoldCentralAction
import Hindman168.UnitTorusCompactObservableSelection
import Mathlib.Topology.CompactOpen

/-! Actual orbital observable family is compact in the uniform norm.
One finite Fourier family works for ALL original unit observables and cosets. -/

namespace Hindman168
open scoped Manifold ContDiff Classical
universe u

noncomputable def nativeCentralOrbitObservable {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ, ℂ) → (D.G ⧸ D.Γ) → C(UnitAddTorus (nativeNilmanifoldCenterIndex D), ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact fun F q => ⟨fun a => F (nativeNilmanifoldCentralAction D a q),
    F.continuous.comp ((native_nilmanifold_central_action_continuous D).comp
      (continuous_id.prodMk continuous_const))⟩

theorem native_central_orbit_observable_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : D.G ⧸ D.Γ) (a : UnitAddTorus (nativeNilmanifoldCenterIndex D)),
      nativeCentralOrbitObservable D F q a = F (nativeNilmanifoldCentralAction D a q) := by
  intro F q a
  rfl

theorem native_central_orbit_observable_continuous {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : C(D.G ⧸ D.Γ, ℂ) × (D.G ⧸ D.Γ) => nativeCentralOrbitObservable D p.1 p.2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp ((continuous_fst.fst).prodMk
    ((native_nilmanifold_central_action_continuous D).comp
      (continuous_snd.prodMk continuous_fst.snd)))

theorem native_central_unit_orbit_family_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact ((fun p : C(D.G ⧸ D.Γ, ℂ) × (D.G ⧸ D.Γ) => nativeCentralOrbitObservable D p.1 p.2) ''
      (unitLipschitzObservables (D.G ⧸ D.Γ) ×ˢ Set.univ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  exact ((unit_lipschitz_observables_compact (D.G ⧸ D.Γ)).prod isCompact_univ).image
    (native_central_orbit_observable_continuous D)

theorem native_central_unit_orbit_finite_fourier_family {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (ε : ℝ) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ A : Finset ((nativeNilmanifoldCenterIndex D → ℤ) →₀ ℂ),
      ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∀ q : D.G ⧸ D.Γ,
        ∃ c ∈ A, ‖nativeCentralOrbitObservable D F q - c.sum (fun k a => a •
          (UnitAddTorus.mFourier k : C(UnitAddTorus (nativeNilmanifoldCenterIndex D), ℂ)))‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A, hA⟩ := unit_torus_compact_uniform_fourier_family (nativeNilmanifoldCenterIndex D) _
    (native_central_unit_orbit_family_compact D) ε hε
  refine ⟨A, ?_⟩
  intro F hF q
  exact hA _ ⟨(F,q), ⟨hF, Set.mem_univ q⟩, rfl⟩

end Hindman168
