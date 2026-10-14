import Hindman168.NativeRationalZeroInverseNatReduction
import Hindman168.NativeRationalTerminalFourierSelection

/-! TRUE original degree-induction alternative: the zero branch yields a
genuine ORIGINAL nonzero horizontal obstruction; only the bounded actual
NONZERO terminal-frequency branch remains. This is NOT a complete inverse. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_inverse_bounded_alternative {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (σ : Type*) [Fintype σ]
    (hInverse : NativeRationalWeightedInverseStatement (nativeRationalTerminalQuotientData D L)
      (nativeTerminalRationalLieFiltration D L) σ) (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
    letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ M : ℕ, 0 < M ∧ ∃ S : Finset (nativeRationalTerminalIndex D L → ℤ),
      (∀ k ∈ S, (∑ i, (k i).natAbs) ≤ M) ∧
      ∀ p : RoughVectorMvPolynomial σ D.E, RoughVectorMvWeightedDegree L.layer p 0 →
        ∀ N : ℕ, 0 < N → ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D (scalarMvIntegerCube σ N) (nativeMvPolynomialOrbit D p) H‖ →
          (∃ χ : D.E →L[ℝ] ℝ,
            RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧ ‖χ‖ ≤ (M : ℝ) ∧
            χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (M : ℝ) ∧
            (∀ J : σ → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)) ∧
            ∀ J : σ → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
                (roughVectorMvProjection χ.toLinearMap p) ℓ J : ℝ) : UnitAddCircle)‖ ≤ (M : ℝ)) ∨
          ∃ k ∈ S, k ≠ 0 ∧ η ≤ ‖finiteComplexSetMean (scalarMvIntegerCube σ N)
            (fun x => nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p x))‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).E := borel (nativeRationalTerminalQuotientData D L).E
  letI : MeasurableSpace (nativeRationalTerminalQuotientData D L).G := borel (nativeRationalTerminalQuotientData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨η,hη,hη1,Mk,hMk,S,hS,hSelect⟩ := native_rational_terminal_fourier_bounded_alternative D L δ hδ
  obtain ⟨Mc,hMc,hZero⟩ := native_rational_zero_inverse_nat_reduction D L σ hInverse η hη
  let M : ℕ := max Mc Mk
  have hCM : (Mc : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_max_left Mc Mk
  refine ⟨η,hη,hη1,M,hMc.trans_le (le_max_left _ _),S,?_,?_⟩
  · exact fun k hk => (hS k hk).trans (le_max_right _ _)
  · intro p hp N hN H hH hLarge
    rcases hSelect (scalarMvIntegerCube σ N) (nativeMvPolynomialOrbit D p) H hH hLarge with h0 | hk
    · left
      obtain ⟨χ,hHor,hNorm,_,hCoeffs,hBinomial⟩ := hZero p hp N hN H hH h0
      have hn := hNorm.trans hCM
      exact ⟨χ,hHor,hn,rough_native_norm_bounded_horizontal_grid_mem D.Γ (M : ℝ)
        (Nat.cast_nonneg M) χ hn hHor,fun J hJ => (hCoeffs J hJ).trans hCM,
        fun J hJ => (hBinomial J hJ).trans hCM⟩
    · exact Or.inr hk

end Hindman168
