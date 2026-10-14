import Hindman168.NativeOriginalTerminalFourierReconstruction
import Hindman168.NativeNilmanifoldFiniteDiscrepancy

/-! Nonzero ACTUAL ORIGINAL terminal frequency retains SAME original
finite sample average, by its genuine ORIGINAL canonical Haar mean zero. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_nilmanifold_finite_discrepancy_nonzero_terminal_projection {s : ℕ} {α : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (a : Finset α) (f : α → D.G ⧸ D.Γ)
    (k : nativeOriginalTerminalIndex D d → ℤ) (hk : k ≠ 0) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeNilmanifoldFiniteDiscrepancy D a f (nativeOriginalTerminalFourierProjection D d hd k F) =
        finiteComplexSetMean a (fun x => nativeOriginalTerminalFourierProjection D d hd k F (f x)) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  change finiteComplexSetMean a (fun x => nativeOriginalTerminalFourierProjection D d hd k F (f x)) -
    (∫ q, nativeOriginalTerminalFourierProjection D d hd k F q ∂nativeNilmanifoldQuotientProbability D) = _
  rw [native_original_terminal_fourier_projection_nonzero_mean D d hd k hk,sub_zero]

end Hindman168
