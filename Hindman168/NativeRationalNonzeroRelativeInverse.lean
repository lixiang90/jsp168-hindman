import Hindman168.NativeRationalNonzeroChildInverse
import Hindman168.NativeRationalCompactRelativePolynomial

/-! Actual nonzero relative horizontal character/grid/operator and BOTH raw coefficient bounds under genuine child inverse induction. Original group reconstruction remains open. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_nonzero_relative_inverse {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (hInverse : NativeRationalWeightedInverseStatement (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (η : ℝ) (hη : 0 < η) :
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ A : ℝ, 0 < A ∧
      ∀ (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
        (h : ℤ) (N : ℕ), 0 < N → ∀ H ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        η ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
          nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n+h)) *
            star (nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n))))‖ →
        ∃ χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ,
          RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
            (nativeRationalRelativeData D L 1).Γ χ.toLinearMap ∧ ‖χ‖ ≤ A ∧
          χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := (nativeRationalRelativeData D L 1).I)
            (nativeRationalRelativeData D L 1).Γ A ∧
          (∀ J : Unit → ℕ, 0 < (∑ i, J i) →
            (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
              (roughVectorMvProjection χ.toLinearMap (nativeRationalCompactRelativePolynomial D L p hp h)) : ℝ) :
                UnitAddCircle)‖ ≤ A) ∧
          ∀ J : Unit → ℕ, 0 < (∑ i, J i) →
            (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
              (roughVectorMvProjection χ.toLinearMap (nativeRationalCompactRelativePolynomial D L p hp h))
                ℓ J : ℝ) : UnitAddCircle)‖ ≤ A := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨M,hM,hChild⟩ := native_rational_nonzero_child_inverse D L hdeg hInverse k hk η hη
  have hMReal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hBudget := native_rational_terminal_character_budget_ge (nativeRationalRelativeData D L 1)
    (nativeRelativeRationalLieFiltration D L) (M : ℝ) hMReal.le
  refine ⟨nativeRationalTerminalCharacterBudget (nativeRationalRelativeData D L 1)
    (nativeRelativeRationalLieFiltration D L) (M : ℝ),hMReal.trans_le hBudget,?_⟩
  intro p hp h N hN H hH hLarge
  obtain ⟨χ,hHor,hNorm,_,hCoeffs,hBinomial⟩ := hChild p hp h N hN H hH hLarge
  refine ⟨nativeRationalTerminalCharacterPullback (nativeRationalRelativeData D L 1)
      (nativeRelativeRationalLieFiltration D L) χ,
    native_rational_terminal_character_pullback_horizontal _ _ χ hHor,
    native_rational_terminal_character_pullback_bound _ _ (M : ℝ) hMReal.le χ hNorm,
    native_rational_terminal_character_pullback_grid _ _ (M : ℝ) hMReal.le χ hNorm hHor,?_,?_⟩
  · intro J hJ
    rw [native_rational_compact_relative_character_coefficient]
    exact (hCoeffs J hJ).trans hBudget
  · intro J hJ
    rw [native_rational_compact_relative_character_binomial]
    exact (hBinomial J hJ).trans hBudget

end Hindman168
