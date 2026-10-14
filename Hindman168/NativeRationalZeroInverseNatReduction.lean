import Hindman168.NativeRationalZeroInverseReduction

/-! Actual original zero-mode character reconstruction has a fixed NATURAL
budget and ORIGINAL finite grid, suitable for the full degree induction. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_zero_inverse_nat_reduction {s ℓ : ℕ}
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
    ∃ M : ℕ, 0 < M ∧ ∀ p : RoughVectorMvPolynomial σ D.E,
      RoughVectorMvWeightedDegree L.layer p 0 → ∀ N : ℕ, 0 < N →
        ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          η ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube σ N)
            (nativeMvPolynomialOrbit D p) (nativeRationalTerminalFourierProjection D L 0 H)‖ →
          ∃ χ : D.E →L[ℝ] ℝ,
            RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (M : ℝ) ∧
            χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (M : ℝ) ∧
            (∀ J : σ → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)) ∧
            ∀ J : σ → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
                (roughVectorMvProjection χ.toLinearMap p) ℓ J : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A,hA,hParent⟩ := native_rational_zero_inverse_induction_reduction D L σ hInverse η hη
  let M : ℕ := ⌈A⌉₊+1
  have hAM : A ≤ (M : ℝ) := by
    apply (Nat.le_ceil A).trans
    dsimp only [M]
    exact_mod_cast Nat.le_add_right (⌈A⌉₊) 1
  refine ⟨M,by dsimp only [M]; omega,?_⟩
  intro p hp N hN H hH hLarge
  obtain ⟨χ,hHor,hNorm,_,hCoeffs,hBinomial⟩ := hParent p hp N hN H hH hLarge
  have hNormM := hNorm.trans hAM
  refine ⟨χ,hHor,hNormM,
    rough_native_norm_bounded_horizontal_grid_mem D.Γ (M : ℝ) (Nat.cast_nonneg M) χ hNormM hHor,?_,?_⟩
  · exact fun J hJ => (hCoeffs J hJ).trans hAM
  · exact fun J hJ => (hBinomial J hJ).trans hAM

end Hindman168
