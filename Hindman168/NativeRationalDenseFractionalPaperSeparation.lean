import Hindman168.NativeRationalDensePaperSeparation
import Hindman168.NativeRationalDenseFractionalInput

/-! Actual nonzero-frequency signal yields a bounded fractional bracket
input on SAME refined useful shifts, preserving BOTH higher P/Q tables,
the SAME bounded natural M, actual relative character and original scale.
The quantitative bracket alternative itself is not assumed or concluded. -/
namespace Hindman168
open MeasureTheory Polynomial
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_dense_fractional_paper_separation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (hInverse : NativeRationalWeightedInverseStatement (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
    letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ A B ρ H Z : ℝ, ∃ S T : ℕ, 0 < A ∧ 0 < B ∧ 0 < ρ ∧ 0 ≤ H ∧ 0 ≤ Z ∧ 0 < S ∧ 0 < T ∧
      ∃ K : ℕ,
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
            (∀ j : ℕ, 3 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ B) ∧
            (∀ j : ℕ, 3 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*scalarPolynomialBinomialCoefficient
                (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ j : ℝ) : UnitAddCircle)‖ ≤ B) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ B) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*scalarPolynomialBinomialCoefficient
                (nativeRationalCompactDiagonalScalar D L p χ) ℓ j : ℝ) : UnitAddCircle)‖ ≤ B) ∧
            ∃ b : NativeRationalFirstLayerIndex D L → ℤ,
              (∀ i, |(b i : ℝ)| ≤ (K : ℝ)) ∧
              (∀ i, |nativeRationalCompactBracketFrequency D L p i| ≤ H) ∧
              (∀ i, |nativeRationalCompactBracketCoefficient D L p χ M i| ≤ Z) ∧
              ∃ V : Finset ℕ, V.Nonempty ∧ ρ*(N : ℝ) ≤ V.card ∧
                ∀ h ∈ V, 0 < h ∧ h < N ∧ NativeRationalRelativeCoefficientBounds D L p hp h χ N B ∧
                  (N : ℝ)*‖((scalarFractionalBracket
                    (nativeRationalCompactBracketBeta D L p χ M b) (nativeRationalCompactBracketAlpha D L p hp χ M)
                    (nativeRationalCompactBracketCoefficient D L p χ M) (nativeRationalCompactBracketFrequency D L p)
                    (h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ B := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A,B,ρ,S,T,hA,hB,hρ,hS,hT,C,hData⟩ := native_rational_dense_paper_separation D L hdeg hInverse k hk δ hδ hδ1
  obtain ⟨ρ',hρ',K,hRefine⟩ := native_rational_dense_fractional_input D L ρ hρ
  obtain ⟨H,hH,hFrequency⟩ := native_rational_compact_bracket_frequency_bound D L
  obtain ⟨Z,hZ,hCoefficient⟩ := native_rational_compact_bracket_coefficient_bound D L A hA.le S
  refine ⟨A,B,ρ',H,Z,S,T,hA,hB,hρ',hH,hZ,hS,hT,K,C,?_⟩
  intro p hp N hTN F hF hlarge hmean
  obtain ⟨χ,hχ,hHor,hNorm,M,hM,hMS,hQM,hQB,hPM,hPB,U,hU,hsize,hUseful⟩ := hData p hp N hTN F hF hlarge hmean
  obtain ⟨b,hb,V,hVU,hV,hsizeV,hBracket⟩ := hRefine p hp χ hHor.2.1 M N B U hU hsize
    (fun h hh => (hUseful h hh).2.2.2)
  refine ⟨χ,hχ,hHor,hNorm,M,hM,hMS,hQM,hQB,hPM,hPB,b,hb,hFrequency p,
    hCoefficient p χ hNorm M hMS,V,hV,hsizeV,?_⟩
  intro h hh
  obtain ⟨hpos,hlt,hBounds,_⟩ := hUseful h (hVU hh)
  exact ⟨hpos,hlt,hBounds,hBracket h hh⟩

end Hindman168
