import Hindman168.NativeRationalTerminalFourierProjection

/-! Actual terminal FourierGroupAction for ANY original finite rational Lie filtration.
All original central/rational/lattice/action/canonical-Haar inputs are
PROVED using SAME actual terminal layer and SAME original specified metric. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_fourier_group_equivariant {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (z : nativeRationalFilteredGroupLayer D L ℓ) (q : D.G ⧸ D.Γ),
      nativeRationalTerminalFourierProjection D L k F ((z : D.G) • q) =
        UnitAddTorus.mFourier k (nativeRationalTerminalTorusProjection D L z) *
          nativeRationalTerminalFourierProjection D L k F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F z q
  exact (congrArg (fun y : D.G ⧸ D.Γ => nativeRationalTerminalFourierProjection D L k F y)
    (native_rational_terminal_action_mk D L z q).symm).trans
    (native_rational_terminal_fourier_projection_equivariant D L k F q
      (nativeRationalTerminalTorusProjection D L z))

theorem native_rational_terminal_fourier_zero_group_invariant {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (z : nativeRationalFilteredGroupLayer D L ℓ) (q : D.G ⧸ D.Γ),
      nativeRationalTerminalFourierProjection D L 0 F ((z : D.G) • q) =
        nativeRationalTerminalFourierProjection D L 0 F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F z q
  rw [native_rational_terminal_fourier_group_equivariant,UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,one_mul]

end Hindman168
