import Hindman168.NativeRationalDensePaperSeparation

/-! Complete ACTUAL degree-two paper scalar separation with NO child inverse
premise. Bracket alternative/original nonzero inverse remain unproved. -/
namespace Hindman168
open MeasureTheory Polynomial
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_degree_two_dense_paper_separation {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D 2)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ A B ρ : ℝ, ∃ S T : ℕ, 0 < A ∧ 0 < B ∧ 0 < ρ ∧ 0 < S ∧ 0 < T ∧
      ∃ C : Finset ((nativeRationalRelativeData D L 1).E →L[ℝ] ℝ),
      ∀ (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
        (N : ℕ), T ≤ N → ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        4 ≤ δ^2*(N : ℝ) →
        δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
          nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n)))‖ →
        ∃ χ ∈ C,
          RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
            (nativeRationalRelativeData D L 1).Γ χ.toLinearMap ∧ ‖χ‖ ≤ A ∧
          ∃ M : ℕ, 0 < M ∧ M ≤ S ∧
            (∀ j : ℕ, 3 ≤ j → j ≤ 2 → (N : ℝ)^j*
              ‖(((M : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ B) ∧
            (∀ j : ℕ, 3 ≤ j → j ≤ 2 → (N : ℝ)^j*
              ‖(((M : ℝ)*scalarPolynomialBinomialCoefficient
                (nativeRationalCompactNonlinearScalar D L p hp χ) 2 j : ℝ) : UnitAddCircle)‖ ≤ B) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ 2 → (N : ℝ)^j*
              ‖(((M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ B) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ 2 → (N : ℝ)^j*
              ‖(((M : ℝ)*scalarPolynomialBinomialCoefficient
                (nativeRationalCompactDiagonalScalar D L p χ) 2 j : ℝ) : UnitAddCircle)‖ ≤ B) ∧
            ∃ U : Finset ℕ, U.Nonempty ∧ ρ*(N : ℝ) ≤ U.card ∧
              ∀ h ∈ U, 0 < h ∧ h < N ∧ NativeRationalRelativeCoefficientBounds D L p hp h χ N B ∧
                (N : ℝ)*‖(((M : ℝ)*((nativeRationalCompactDiagonalScalar D L p χ).eval 1+
                  scalarPolynomialBinomialCoefficient (nativeRationalCompactNonlinearScalar D L p hp χ) 2 2*(h : ℝ)+
                  nativeRationalCompactCommutatorSlope D L p χ h) : ℝ) : UnitAddCircle)‖ ≤ B := by
  exact native_rational_dense_paper_separation D L (by omega)
    (native_rational_weighted_inverse_degree_one (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit) k hk δ hδ hδ1

end Hindman168
