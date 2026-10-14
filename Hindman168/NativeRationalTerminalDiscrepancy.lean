import Hindman168.NativeRationalTerminalFourierReconstruction
import Hindman168.NativeNilmanifoldFiniteDiscrepancy

/-! Actual terminal Discrepancy for ANY original finite rational Lie filtration.
All original central/rational/lattice/action/canonical-Haar inputs are
PROVED using SAME actual terminal layer and SAME original specified metric. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_rational_finite_discrepancy_nonzero_terminal_projection {s ℓ : ℕ} {α : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (a : Finset α) (f : α → D.G ⧸ D.Γ)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeNilmanifoldFiniteDiscrepancy D a f (nativeRationalTerminalFourierProjection D L k F) =
        finiteComplexSetMean a (fun x => nativeRationalTerminalFourierProjection D L k F (f x)) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  change finiteComplexSetMean a (fun x => nativeRationalTerminalFourierProjection D L k F (f x)) -
    (∫ q, nativeRationalTerminalFourierProjection D L k F q ∂nativeNilmanifoldQuotientProbability D) = _
  rw [native_rational_terminal_fourier_projection_nonzero_mean D L k hk,sub_zero]

end Hindman168
