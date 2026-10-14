import Hindman168.NativeOriginalTerminalAction
import Hindman168.UnitTorusCompactObservableSelection
import Mathlib.Topology.CompactOpen

/-! ACTUAL ORIGINAL TERMINAL-LAYER specialization. All action inputs are
proved from original terminal centrality/rationality/lattice coordinates.
The torus index is the ACTUAL terminal-layer rank.
 Actual orbital observable family is compact in the uniform norm.
One finite Fourier family works for ALL original unit observables and cosets. -/

namespace Hindman168
open scoped Manifold ContDiff Classical
universe u

noncomputable def nativeOriginalTerminalOrbitObservable {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ, ℂ) → (D.G ⧸ D.Γ) → C(UnitAddTorus (nativeOriginalTerminalIndex D d), ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact fun F q => ⟨fun a => F (nativeOriginalTerminalAction D d hd a q),
    F.continuous.comp ((native_original_terminal_action_continuous D d hd).comp
      (continuous_id.prodMk continuous_const))⟩

theorem native_original_terminal_orbit_observable_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : D.G ⧸ D.Γ) (a : UnitAddTorus (nativeOriginalTerminalIndex D d)),
      nativeOriginalTerminalOrbitObservable D d hd F q a = F (nativeOriginalTerminalAction D d hd a q) := by
  intro F q a
  rfl

theorem native_original_terminal_orbit_observable_continuous {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : C(D.G ⧸ D.Γ, ℂ) × (D.G ⧸ D.Γ) => nativeOriginalTerminalOrbitObservable D d hd p.1 p.2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp ((continuous_fst.fst).prodMk
    ((native_original_terminal_action_continuous D d hd).comp
      (continuous_snd.prodMk continuous_fst.snd)))

theorem native_original_terminal_unit_orbit_family_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact ((fun p : C(D.G ⧸ D.Γ, ℂ) × (D.G ⧸ D.Γ) => nativeOriginalTerminalOrbitObservable D d hd p.1 p.2) ''
      (unitLipschitzObservables (D.G ⧸ D.Γ) ×ˢ Set.univ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  exact ((unit_lipschitz_observables_compact (D.G ⧸ D.Γ)).prod isCompact_univ).image
    (native_original_terminal_orbit_observable_continuous D d hd)

theorem native_original_terminal_unit_orbit_finite_fourier_family {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (ε : ℝ) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ A : Finset ((nativeOriginalTerminalIndex D d → ℤ) →₀ ℂ),
      ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∀ q : D.G ⧸ D.Γ,
        ∃ c ∈ A, ‖nativeOriginalTerminalOrbitObservable D d hd F q - c.sum (fun k a => a •
          (UnitAddTorus.mFourier k : C(UnitAddTorus (nativeOriginalTerminalIndex D d), ℂ)))‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A, hA⟩ := unit_torus_compact_uniform_fourier_family (nativeOriginalTerminalIndex D d) _
    (native_original_terminal_unit_orbit_family_compact D d hd) ε hε
  refine ⟨A, ?_⟩
  intro F hF q
  exact hA _ ⟨(F,q), ⟨hF, Set.mem_univ q⟩, rfl⟩

end Hindman168
