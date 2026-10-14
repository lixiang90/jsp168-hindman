import Hindman168.NativeBasepointObservable
import Hindman168.NativeRationalTerminalFourierProjection

/-! Original translations commute with the true rational terminal Fourier projections. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_rational_basepoint_observable_terminal_projection {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (r : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeRationalTerminalFourierProjection D L k (nativeBasepointObservable D r F) =
      nativeBasepointObservable D r (nativeRationalTerminalFourierProjection D L k F) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  ext q
  rw [native_rational_terminal_fourier_projection_apply,native_basepoint_observable_apply,
    native_rational_terminal_fourier_projection_apply]
  apply integral_congr_ae
  filter_upwards with a
  simp only [native_basepoint_observable_apply,native_rational_terminal_action_commutes]

end Hindman168
