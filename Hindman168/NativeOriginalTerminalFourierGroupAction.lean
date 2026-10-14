import Hindman168.NativeOriginalTerminalFourierProjection

/-! ACTUAL original terminal GROUP translations satisfy the genuine
original terminal Fourier eigencharacter law, including zero-mode invariance. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_original_terminal_fourier_group_equivariant {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (z : roughStretchedLowerCentralFiltration D.G d (s*d)) (q : D.G ⧸ D.Γ),
      nativeOriginalTerminalFourierProjection D d hd k F ((z : D.G) • q) =
        UnitAddTorus.mFourier k (nativeOriginalTerminalTorusProjection D d hd z) *
          nativeOriginalTerminalFourierProjection D d hd k F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F z q
  exact (congrArg (fun y : D.G ⧸ D.Γ => nativeOriginalTerminalFourierProjection D d hd k F y)
    (native_original_terminal_action_mk D d hd z q).symm).trans
    (native_original_terminal_fourier_projection_equivariant D d hd k F q
      (nativeOriginalTerminalTorusProjection D d hd z))

theorem native_original_terminal_fourier_zero_group_invariant {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (z : roughStretchedLowerCentralFiltration D.G d (s*d)) (q : D.G ⧸ D.Γ),
      nativeOriginalTerminalFourierProjection D d hd 0 F ((z : D.G) • q) =
        nativeOriginalTerminalFourierProjection D d hd 0 F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F z q
  rw [native_original_terminal_fourier_group_equivariant,UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,one_mul]

end Hindman168
