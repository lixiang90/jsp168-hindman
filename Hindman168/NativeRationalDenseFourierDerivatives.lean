import Hindman168.NativeRationalTerminalFourierProjection
import Hindman168.NativeCentralPolynomialProjection
import Hindman168.FiniteDenseDerivativeMeans

/-! Actual native Fourier signals yield a dense set of genuine derivative
means at their true retained sample lengths. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_dense_fourier_derivatives {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (δ : ℝ) (hδ : 0 < δ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (p : RoughVectorMvPolynomial Unit D.E) (N : ℕ), 0 < N →
      ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), 4 ≤ δ^2*(N : ℝ) →
      δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
        nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n)))‖ →
      ∃ T : Finset ℕ, δ^2/8*(N : ℝ) ≤ T.card ∧
        ∀ h ∈ T, 0 < h ∧ h < N ∧ 0 < N-h ∧ δ^2/8*(N : ℝ) ≤ (N-h : ℕ) ∧
          δ^2/8 ≤ ‖finiteComplexSetMean (Finset.Ico 0 ((N-h : ℕ) : ℤ)) (fun n =>
            nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n+h)) *
              star (nativeRationalTerminalFourierProjection D L k F
                (nativeMvPolynomialOrbit D p (fun _ => n))))‖ := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro p N hN F hF hlarge hmean
  have hnorm : ‖nativeRationalTerminalFourierProjection D L k F‖ ≤ 1 :=
    (native_rational_terminal_fourier_projection_norm D L k F).trans
      ((ContinuousMap.norm_le F zero_le_one).mpr hF.2)
  exact finite_complex_dense_integer_derivative_means
    (fun n : ℤ => nativeRationalTerminalFourierProjection D L k F
      (nativeMvPolynomialOrbit D p (fun _ : Unit => n))) N hN
    (fun n _ _ => ((nativeRationalTerminalFourierProjection D L k F).norm_coe_le_norm _).trans hnorm)
    δ hδ hlarge hmean

end Hindman168
