import Hindman168.NativeRationalTerminalZeroObservable

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_zero_observable_sub {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := (nativeRationalTerminalQuotientData D L).metric
    letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
      (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
    ∀ H K : C(D.G ⧸ D.Γ,ℂ), nativeRationalTerminalZeroObservable D L (H-K) =
      nativeRationalTerminalZeroObservable D L H - nativeRationalTerminalZeroObservable D L K := by
  intro H K
  ext y
  obtain ⟨q,rfl⟩ := native_rational_terminal_factor_surjective D L y
  simp only [native_rational_terminal_zero_observable_apply,ContinuousMap.sub_apply,
    native_rational_terminal_fourier_projection_sub]

end Hindman168
