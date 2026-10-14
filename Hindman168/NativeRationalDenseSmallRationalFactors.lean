import Hindman168.NativeRationalDenseNonlinearityFactorization
import Hindman168.NativeRationalNonlinearityExactFactorization
import Hindman168.NativeRationalZeroPairingCompleteTables
import Hindman168.NativeRationalNonlinearSmallRationalFactors

/-! SAME original Fourier signal yields FULL original inverse OR genuine
smaller nonlinearity, COMPLETE native nonlinear tables and ACTUAL small /
rational factors, finite original lattice residues and error variation.
No large child correlation or arbitrary right-quotient action is assumed. -/
namespace Hindman168
open MeasureTheory Polynomial
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_dense_small_rational_factors {s ℓ : ℕ}
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
            (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*(nativeRationalCompactNonlinearScalar D L p hp χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*scalarPolynomialBinomialCoefficient
                (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).coeff j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            (∀ j : ℕ, 2 ≤ j → j ≤ ℓ → (N : ℝ)^j*
              ‖(((M : ℝ)*scalarPolynomialBinomialCoefficient
                (nativeRationalCompactDiagonalScalar D L p χ) ℓ j : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
            ((N : ℝ)*‖(((M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).eval 1 : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
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
                  (∃ (z : ℕ → ℤ) (E : ℝ[X]) (pK : RoughVectorMvPolynomial Unit D.E),
      E.natDegree ≤ j ∧ E.coeff 0=0 ∧ E.coeff 1=0 ∧
      (∀ i : ℕ, 2 ≤ i → i ≤ j → (M : ℝ)*(N : ℝ)^i*|E.coeff i| ≤ (A : ℝ)) ∧
      RoughVectorMvWeightedDegree K.layer pK 0 ∧ RoughVectorMvDegreeLE pK ℓ ∧
      (∀ t : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) p (fun _ => t)) =
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (E.eval t • y)*
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval t • y)*
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK (fun _ => t))) ∧
      (∀ (x t H : ℝ), 0 ≤ H → |x| ≤ (N : ℝ) → |t| ≤ (N : ℝ) → |x-t| ≤ H →
        (M : ℝ)*|E.eval x-E.eval t| ≤ ((j+1 : ℕ) : ℝ)^2*(A : ℝ)*(H/(N : ℝ))) ∧
      (∀ t : ℝ, |t| ≤ (N : ℝ) → |E.eval t| ≤ ((j+1 : ℕ) : ℝ)^2*(A : ℝ)) ∧
      (∀ n : ℕ, ∃ m ∈ Finset.range (M*q),
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval (n : ℝ) • y) : D.G ⧸ D.Γ) =
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y) : D.G ⧸ D.Γ)) ∧
      ∀ a t : ℕ,
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval ((a+M*q*t : ℕ) : ℝ) • y) : D.G ⧸ D.Γ) =
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) ((scalarNonlinearRationalPart j M z).eval (a : ℝ) • y) : D.G ⧸ D.Γ)) ∧
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
  obtain ⟨A0,Q,S0,T0,hA0,hQ,hS0,hT0,ρ,hρ,C,hData⟩ :=
    native_rational_dense_nonlinearity_factorization D L hdeg hInverse k hk δ hδ hδ1
  have hρ1 : 0 < min ρ 1 := lt_min hρ (by norm_num)
  obtain ⟨A1,S,T1,hA1,hS,hT1,hComplete⟩ := native_rational_zero_pairing_complete_tables
    D L hdeg (min ρ 1) (A0 : ℝ) S0 hρ1 (min_le_right _ _) (Nat.cast_nonneg _) hS0
  let A := 2*A1+A0+1
  let T := T0+T1+1
  have h0A : (A0 : ℝ) ≤ A := by exact_mod_cast (show A0 ≤ A by dsimp only [A]; omega)
  have h1A : (A1 : ℝ) ≤ A := by exact_mod_cast (show A1 ≤ A by dsimp only [A]; omega)
  have h2A : 2*(A1 : ℝ) ≤ A := by exact_mod_cast (show 2*A1 ≤ A by dsimp only [A]; omega)
  refine ⟨A,Q,S,T,by dsimp only [A]; omega,hQ,hS,by dsimp only [T]; omega,ρ,hρ,C,?_⟩
  intro p hp N hTN F hF hlarge hmean
  have hTN0 : T0 ≤ N := (show T0 ≤ T by dsimp only [T]; omega).trans hTN
  have hTN1 : T1 ≤ N := (show T1 ≤ T by dsimp only [T]; omega).trans hTN
  have hN : 0 < N := hT0.trans_le hTN0
  rcases hData p hp N hTN0 F hF hlarge hmean with hOriginal | hRemaining
  · exact Or.inl hOriginal
  · obtain ⟨χ,hχC,hHor,hNorm,M0,hM0,hMS0,hQM0,_hQB0,hPM0,hPB0,b,hb,hDiff,hZero,hPair,
        _K0,_hLayers0,_hRank0,_hDrop0,_hGeom0,V,hV,hsize,hUseful⟩ := hRemaining
    have hdense : min ρ 1*(N : ℝ) ≤ V.card :=
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg N)).trans hsize
    obtain ⟨M,hM,hMS,hQM,hQB,hPM,hPB,hEval⟩ := hComplete p hp χ hPair M0 hM0 hMS0 N hTN1
      hQM0 hPM0 hPB0 b V hdense (fun h hh => ⟨(hUseful h hh).2.1,(hUseful h hh).2.2.2⟩)
    let K := nativeRationalNonlinearKernelFiltration D L χ hHor hPair
    obtain ⟨hDrop,j,y,q,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,hUniversal⟩ :=
      native_rational_nonlinearity_exact_factorization D L hdeg χ hHor hPair hDiff
    obtain ⟨z,E,pK,hED,hE0,hE1,hSmall,hWeighted,hDegree,hExact,hVar,hValue,hResidues,hPeriod⟩ :=
      native_rational_nonlinear_small_rational_factors D L χ hHor hPair p hp j hj2 hjL y hy hFy hHigher
        q M N hq hM hN hpow (A1 : ℝ) (Nat.cast_nonneg _) hQM
    have hVarA : ∀ (x t H : ℝ), 0 ≤ H → |x| ≤ (N : ℝ) → |t| ≤ (N : ℝ) → |x-t| ≤ H →
        (M : ℝ)*|E.eval x-E.eval t| ≤ ((j+1 : ℕ) : ℝ)^2*(A : ℝ)*(H/(N : ℝ)) := by
      intro x t H hH hx ht hxt
      exact (hVar x t H hH hx ht hxt).trans (by
        have hh := mul_le_mul_of_nonneg_left h1A (sq_nonneg ((j+1 : ℕ) : ℝ))
        exact mul_le_mul_of_nonneg_right hh (div_nonneg hH (Nat.cast_nonneg N)))
    have hValueA : ∀ t : ℝ, |t| ≤ (N : ℝ) → |E.eval t| ≤ ((j+1 : ℕ) : ℝ)^2*(A : ℝ) :=
      fun t ht => (hValue t ht).trans (mul_le_mul_of_nonneg_left h1A (sq_nonneg ((j+1 : ℕ) : ℝ)))
    refine Or.inr ⟨χ,hχC,hHor,hNorm.trans h0A,M,hM,hMS,
      (fun j hj hjL => (hQM j hj hjL).trans h1A),
      (fun j hj hjL => (hQB j hj hjL).trans h1A),
      (fun j hj hjL => (hPM j hj hjL).trans h1A),
      (fun j hj hjL => (hPB j hj hjL).trans h1A),hEval.trans h1A,
      b,(fun i => (hb i).trans h0A),hDiff,hZero,hPair,
      K,native_rational_nonlinear_kernel_filtration_layer D L χ hHor hPair,
      native_rational_nonlinear_kernel_filtration_two_dimension_lt D L χ hHor hPair hDiff,
      hDrop,⟨j,y,q,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,
        ⟨z,E,pK,hED,hE0,hE1,(fun i hi hij => (hSmall i hi hij).trans h1A),
          hWeighted,hDegree,hExact,hVarA,hValueA,hResidues,hPeriod⟩,hUniversal⟩,
      V,hV,hsize,?_⟩
    intro h hh
    obtain ⟨hpos,hlt,hRelative,_hBracket⟩ := hUseful h hh
    refine ⟨hpos,hlt,⟨fun J hJ hJL => (hRelative.1 J hJ hJL).trans h0A,
      fun J hJ hJL => (hRelative.2 J hJ hJL).trans h0A⟩,?_⟩
    rw [native_rational_zero_pairing_bracket_affine D L χ hPair p hp M b]
    exact (unit_circle_affine_completed_bound _ _ N h (A1 : ℝ) hlt.le hEval (hQB 2 (by omega) hdeg)).trans h2A

end Hindman168
