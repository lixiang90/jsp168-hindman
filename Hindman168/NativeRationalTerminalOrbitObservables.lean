import Hindman168.NativeRationalTerminalAction
import Hindman168.UnitTorusCompactObservableSelection
import Mathlib.Topology.CompactOpen

/-! Actual terminal OrbitObservables for ANY original finite rational Lie filtration.
All original central/rational/lattice/action/canonical-Haar inputs are
PROVED using SAME actual terminal layer and SAME original specified metric. -/

namespace Hindman168
open scoped Manifold ContDiff Classical
universe u

noncomputable def nativeRationalTerminalOrbitObservable {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ, ℂ) → (D.G ⧸ D.Γ) → C(UnitAddTorus (nativeRationalTerminalIndex D L), ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact fun F q => ⟨fun a => F (nativeRationalTerminalAction D L a q),
    F.continuous.comp ((native_rational_terminal_action_continuous D L).comp
      (continuous_id.prodMk continuous_const))⟩

theorem native_rational_terminal_orbit_observable_apply {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : D.G ⧸ D.Γ) (a : UnitAddTorus (nativeRationalTerminalIndex D L)),
      nativeRationalTerminalOrbitObservable D L F q a = F (nativeRationalTerminalAction D L a q) := by
  intro F q a
  rfl

theorem native_rational_terminal_orbit_observable_continuous {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : C(D.G ⧸ D.Γ, ℂ) × (D.G ⧸ D.Γ) => nativeRationalTerminalOrbitObservable D L p.1 p.2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp ((continuous_fst.fst).prodMk
    ((native_rational_terminal_action_continuous D L).comp
      (continuous_snd.prodMk continuous_fst.snd)))

theorem native_rational_terminal_unit_orbit_family_compact {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact ((fun p : C(D.G ⧸ D.Γ, ℂ) × (D.G ⧸ D.Γ) => nativeRationalTerminalOrbitObservable D L p.1 p.2) ''
      (unitLipschitzObservables (D.G ⧸ D.Γ) ×ˢ Set.univ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  exact ((unit_lipschitz_observables_compact (D.G ⧸ D.Γ)).prod isCompact_univ).image
    (native_rational_terminal_orbit_observable_continuous D L)

theorem native_rational_terminal_unit_orbit_finite_fourier_family {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (ε : ℝ) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ A : Finset ((nativeRationalTerminalIndex D L → ℤ) →₀ ℂ),
      ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∀ q : D.G ⧸ D.Γ,
        ∃ c ∈ A, ‖nativeRationalTerminalOrbitObservable D L F q - c.sum (fun k a => a •
          (UnitAddTorus.mFourier k : C(UnitAddTorus (nativeRationalTerminalIndex D L), ℂ)))‖ < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A, hA⟩ := unit_torus_compact_uniform_fourier_family (nativeRationalTerminalIndex D L) _
    (native_rational_terminal_unit_orbit_family_compact D L) ε hε
  refine ⟨A, ?_⟩
  intro F hF q
  exact hA _ ⟨(F,q), ⟨hF, Set.mem_univ q⟩, rfl⟩

end Hindman168
