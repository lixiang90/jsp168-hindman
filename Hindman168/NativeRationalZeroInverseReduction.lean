import Hindman168.NativeRationalWeightedInverseStatement
import Hindman168.NativeRationalTerminalCharacterPolynomial
import Hindman168.NativeRationalTerminalZeroWeightedPolynomialDetection

/-! TRUE zero-mode quantitative inverse induction step. Its ONLY inverse
premise is the full desired lower-degree conclusion on the ACTUAL child.
Original nonzero character/grid/operator/monomial/binomial conclusions are
proved, not assumed. Full higher-degree/nonzero-frequency inverse stays open. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_zero_inverse_induction_reduction {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (σ : Type*) [Fintype σ]
    (hInverse : NativeRationalWeightedInverseStatement (nativeRationalTerminalQuotientData D L)
      (nativeTerminalRationalLieFiltration D L) σ) (η : ℝ) (hη : 0 < η) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ A : ℝ, 0 < A ∧ ∀ p : RoughVectorMvPolynomial σ D.E,
      RoughVectorMvWeightedDegree L.layer p 0 → ∀ N : ℕ, 0 < N →
        ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          η ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube σ N)
            (nativeMvPolynomialOrbit D p) (nativeRationalTerminalFourierProjection D L 0 H)‖ →
          ∃ χ : D.E →L[ℝ] ℝ,
            RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ A ∧
            χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ A ∧
            (∀ J : σ → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ A) ∧
            ∀ J : σ → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
                (roughVectorMvProjection χ.toLinearMap p) ℓ J : ℝ) : UnitAddCircle)‖ ≤ A := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := (nativeRationalTerminalQuotientData D L).metric
  letI : TopologicalSpace ((nativeRationalTerminalQuotientData D L).G ⧸ (nativeRationalTerminalQuotientData D L).Γ) :=
    (nativeRationalTerminalQuotientData D L).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨θ,hθ,P,hP,hDetect⟩ := native_rational_terminal_zero_weighted_polynomial_detection D L η hη
  obtain ⟨M,hM,hChild⟩ := hInverse θ hθ
  have hMReal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hBudget := native_rational_terminal_character_budget_ge D L (M : ℝ) hMReal.le
  refine ⟨nativeRationalTerminalCharacterBudget D L (M : ℝ),hMReal.trans_le hBudget,?_⟩
  intro p hp N hN H hH hLarge
  obtain ⟨G,hG,hWeight,_,hBad⟩ := hDetect p hp (scalarMvIntegerCube σ N) H hH hLarge
  obtain ⟨χ,hHor,hNorm,_,hCoeffs,hBinomial⟩ := hChild _ hWeight N hN G (hP G hG) hBad.le
  refine ⟨nativeRationalTerminalCharacterPullback D L χ,
    native_rational_terminal_character_pullback_horizontal D L χ hHor,
    native_rational_terminal_character_pullback_bound D L (M : ℝ) hMReal.le χ hNorm,
    native_rational_terminal_character_pullback_grid D L (M : ℝ) hMReal.le χ hNorm hHor,?_,?_⟩
  · intro J hJ
    rw [native_rational_terminal_character_pullback_coefficient]
    exact (hCoeffs J hJ).trans hBudget
  · intro J hJ
    rw [native_rational_terminal_character_pullback_binomial D L χ hp J]
    exact (hBinomial J hJ).trans hBudget

end Hindman168
