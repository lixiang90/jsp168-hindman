import Hindman168.NativeRationalTerminalFactorTopology
import Hindman168.NativeRationalTerminalFourierGroupAction
import Hindman168.NativeRationalTerminalFourierCompactFamilies

/-! ACTUAL zero terminal Fourier mode descends to the ACTUAL native
terminal quotient/image lattice in its ORIGINAL specified metric. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_fourier_zero_subgroup_invariant {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (H : C(D.G ⧸ D.Γ,ℂ)) (z : nativeRationalTerminalSubgroup D L) (q : D.G ⧸ D.Γ),
      nativeRationalTerminalFourierProjection D L 0 H ((z : D.G) • q) =
        nativeRationalTerminalFourierProjection D L 0 H q := by
  intro H z q
  have hz : z.val ∈ nativeRationalFilteredGroupLayer D L ℓ :=
    Eq.mp (congrArg (fun K : Subgroup D.G => z.val ∈ K) (native_rational_terminal_subgroup_eq D L)) z.property
  exact native_rational_terminal_fourier_zero_group_invariant D L H ⟨z.val,hz⟩ q

noncomputable def nativeRationalTerminalZeroObservable {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalTerminalQuotientData D L).metric
    letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ,ℂ) → C((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ,ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalTerminalQuotientData D L).metric
  letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
  intro H
  exact (native_rational_terminal_factor_metric_openQuotient D L).isQuotientMap.lift
    (f := ⟨nativeRationalTerminalFactorMap D L,(native_rational_terminal_factor_metric_openQuotient D L).continuous⟩)
    (nativeRationalTerminalFourierProjection D L 0 H) (by
      intro q r he
      obtain ⟨z,rfl⟩ := (native_rational_terminal_factor_fiber_iff D L q r).mp he
      exact (native_rational_terminal_fourier_zero_subgroup_invariant D L H z q).symm)

theorem native_rational_terminal_zero_observable_apply {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalTerminalQuotientData D L).metric
    letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
    ∀ (H : C(D.G ⧸ D.Γ,ℂ)) (q : D.G ⧸ D.Γ),
      nativeRationalTerminalZeroObservable D L H (nativeRationalTerminalFactorMap D L q) =
        nativeRationalTerminalFourierProjection D L 0 H q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalTerminalQuotientData D L).metric
  letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
  intro H q
  have he := (native_rational_terminal_factor_metric_openQuotient D L).isQuotientMap.lift_comp
    (f := ⟨nativeRationalTerminalFactorMap D L,(native_rational_terminal_factor_metric_openQuotient D L).continuous⟩)
    (nativeRationalTerminalFourierProjection D L 0 H) (by
      intro q r he
      obtain ⟨z,rfl⟩ := (native_rational_terminal_factor_fiber_iff D L q r).mp he
      exact (native_rational_terminal_fourier_zero_subgroup_invariant D L H z q).symm)
  exact congrArg (fun K : C(D.G ⧸ D.Γ,ℂ) => K q) he

theorem native_rational_terminal_zero_observable_norm {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalTerminalQuotientData D L).metric
    letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
    letI : CompactSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      native_nilmanifold_metric_quotient_compact (nativeRationalTerminalQuotientData D L)
    ∀ H : C(D.G ⧸ D.Γ,ℂ), ‖nativeRationalTerminalZeroObservable D L H‖ ≤ ‖H‖ := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalTerminalQuotientData D L).metric
  letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI : CompactSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    native_nilmanifold_metric_quotient_compact (nativeRationalTerminalQuotientData D L)
  intro H
  apply (ContinuousMap.norm_le _ (norm_nonneg H)).mpr
  intro y
  obtain ⟨q,rfl⟩ := native_rational_terminal_factor_surjective D L y
  rw [native_rational_terminal_zero_observable_apply]
  exact ((nativeRationalTerminalFourierProjection D L 0 H).norm_coe_le_norm q).trans
    (native_rational_terminal_fourier_projection_norm D L 0 H)

end Hindman168
