import Hindman168.NativeRationalDenseCommutatorAlternative
import Hindman168.NativeRationalNonlinearityExactFactorization

/-! SAME actual Fourier signal yields FULL original inverse OR a genuine
smaller rational filtration with STRICTLY smaller nonlinearity AND an
ACTUAL exact source factorization. Removed factor may be UNBOUNDED;
small/rational splitting and correlation transfer remain open. -/
namespace Hindman168
open MeasureTheory Polynomial
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_dense_nonlinearity_factorization {s ℓ : ℕ}
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
    ∃ A Q S T : ℕ, 0 < A ∧ 0 < Q ∧ 0 < S ∧ 0 < T ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : Finset ((nativeRationalRelativeData D L 1).E →L[ℝ] ℝ),
      ∀ (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
        (N : ℕ), T ≤ N → ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        4 ≤ δ^2*(N : ℝ) →
        δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
          nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n)))‖ →
        (∃ χ : D.E →L[ℝ] ℝ, RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧
            ‖χ‖ ≤ (Q : ℝ) ∧ χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (Q : ℝ) ∧
            (∀ J : Unit → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∧
            ∀ J : Unit → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
                (roughVectorMvProjection χ.toLinearMap p) ℓ J : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∨
        (∃ χ ∈ C,
          ∃ hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
            (nativeRationalRelativeData D L 1).Γ χ.toLinearMap, ‖χ‖ ≤ (A : ℝ) ∧
          ∃ M : ℕ, 0 < M ∧ M ≤ S ∧
            (∀ j : ℕ, 3 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            (∀ j : ℕ, 3 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*scalarPolynomialBinomialCoefficient
                (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*scalarPolynomialBinomialCoefficient
                (nativeRationalCompactDiagonalScalar D L p χ) ℓ j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            ∃ b : NativeRationalFirstLayerIndex D L → ℤ,
              (∀ i, |(b i : ℝ)| ≤ (A : ℝ)) ∧
              nativeRationalRelativeDifferenceCharacter D L χ ≠ 0 ∧
              (∀ i, (nativeRationalIntegralCommutatorCharacter D L χ
                hHor.2.1 i).toLinearMap = 0) ∧
              (∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h = 0) ∧
              ∃ K : NativeRationalLieFiltration D ℓ,
                (∀ i, K.layer i = if 2 ≤ i then L.layer i ⊓
                  (nativeRationalDifferenceExtension D L χ).toLinearMap.ker else L.layer i) ∧
                Module.finrank ℝ (K.layer 2) < Module.finrank ℝ (L.layer 2) ∧
                nativeRationalFiltrationNonlinearity D K < nativeRationalFiltrationNonlinearity D L ∧
                (∃ (j : ℕ) (y : D.E) (q : ℕ), 2 ≤ j ∧ j ≤ ℓ ∧ y ∈ L.layer j ∧
                  y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ ∧
                  nativeRationalDifferenceExtension D L χ y=1 ∧
                  L.layer (j+1) ≤ (nativeRationalDifferenceExtension D L χ).toLinearMap.ker ∧
                  0 < q ∧ nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ ∧
                  ∀ (p0 : RoughVectorMvPolynomial Unit D.E), RoughVectorMvWeightedDegree L.layer p0 0 →
                    ∃ pK : RoughVectorMvPolynomial Unit D.E, RoughVectorMvWeightedDegree K.layer pK 0 ∧
                      RoughVectorMvDegreeLE pK ℓ ∧ ∀ x : Unit → ℝ,
                        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p0 x) =
                          nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
                            (MvPolynomial.eval x (unitMvNonlinearPart (roughVectorMvProjection
                              (nativeRationalDifferenceExtension D L χ).toLinearMap p0)) • y) *
                                nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK x)) ∧
              ∃ V : Finset ℕ, V.Nonempty ∧ ρ*(N : ℝ) ≤ V.card ∧
                ∀ h ∈ V, 0 < h ∧ h < N ∧ NativeRationalRelativeCoefficientBounds D L p hp h χ N (A : ℝ) ∧
                  (N : ℝ)*‖((scalarFractionalBracket
                    (nativeRationalCompactBracketBeta D L p χ M b) (nativeRationalCompactBracketAlpha D L p hp χ M)
                    (nativeRationalCompactBracketCoefficient D L p χ M) (nativeRationalCompactBracketFrequency D L p)
                    (h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A,Q,S,T,hA,hQ,hS,hT,ρ,hρ,C,hData⟩ :=
    native_rational_dense_commutator_alternative D L hdeg hInverse k hk δ hδ hδ1
  refine ⟨A,Q,S,T,hA,hQ,hS,hT,ρ,hρ,C,?_⟩
  intro p hp N hTN F hF hlarge hmean
  rcases hData p hp N hTN F hF hlarge hmean with hOriginal | hRemaining
  · exact Or.inl hOriginal
  · obtain ⟨χ,hχC,hHor,hNorm,M,hM,hMS,hQM,hQB,hPM,hPB,b,hb,hDiff,hZero,hPair,V,hV,hsize,hUseful⟩ := hRemaining
    let K := nativeRationalNonlinearKernelFiltration D L χ hHor hPair
    obtain ⟨hDrop,hFactor⟩ := native_rational_nonlinearity_exact_factorization D L hdeg χ hHor hPair hDiff
    exact Or.inr ⟨χ,hχC,hHor,hNorm,M,hM,hMS,hQM,hQB,hPM,hPB,b,hb,hDiff,hZero,hPair,
      K,native_rational_nonlinear_kernel_filtration_layer D L χ hHor hPair,
      native_rational_nonlinear_kernel_filtration_two_dimension_lt D L χ hHor hPair hDiff,
      hDrop,hFactor,V,hV,hsize,hUseful⟩

end Hindman168
