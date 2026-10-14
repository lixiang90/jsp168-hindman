import Hindman168.NativeRationalBracketFullAlternative
import Hindman168.NativeRationalFirstLayerInverseReconstruction
import Hindman168.NativeRationalCommutatorInverseReconstruction
import Hindman168.NativeRationalZeroCommutatorCharacters
import Hindman168.NativeRationalPureDiagonalInverseReconstruction

/-! SAME actual Fourier signal yields FULL original inverse OR a NONZERO
actual F_2 difference character with vanishing commutator pairing. BOTH
higher P/Q tables AND actual dense relative/bracket sample bounds survive.
The remaining nonlinearity filtration/factorization is NOT assumed solved. -/
namespace Hindman168
open MeasureTheory Polynomial
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_dense_commutator_alternative {s ℓ : ℕ}
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
              ∃ V : Finset ℕ, V.Nonempty ∧ ρ*(N : ℝ) ≤ V.card ∧
                ∀ h ∈ V, 0 < h ∧ h < N ∧ NativeRationalRelativeCoefficientBounds D L p hp h χ N (A : ℝ) ∧
                  (N : ℝ)*‖((scalarFractionalBracket
                    (nativeRationalCompactBracketBeta D L p χ M b) (nativeRationalCompactBracketAlpha D L p hp χ M)
                    (nativeRationalCompactBracketCoefficient D L p χ M) (nativeRationalCompactBracketFrequency D L p)
                    (h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) := by
  classical
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A0,B0,ρ,_,Z,S,T,hA0,hB0,hρ,_,hZ,hS,hT,K,C,hData⟩ :=
    native_rational_dense_fractional_paper_separation D L hdeg hInverse k hk δ hδ hδ1
  obtain ⟨R,_,hAlternative⟩ := native_rational_bracket_full_alternative D L Z (min ρ 1) B0 hZ
    (lt_min hρ zero_lt_one) (min_le_right _ _) hB0.le
  obtain ⟨Qv,_,hVector⟩ := native_rational_first_layer_inverse_reconstruction D L (R : ℝ) (R : ℝ)
    (Nat.cast_nonneg R) (Nat.cast_nonneg R)
  obtain ⟨Qc,_,hCommutator⟩ := native_rational_commutator_inverse_reconstruction D L C (R*S) (R : ℝ) (Nat.cast_nonneg R)
  obtain ⟨Qd,_,hDiagonal⟩ := native_rational_pure_diagonal_inverse_reconstruction D L A0 B0 hA0.le hB0.le
  let Q := Qv+Qc+Qd+1
  have hvQ : Qv ≤ Q := by dsimp only [Q]; omega
  have hcQ : Qc ≤ Q := by dsimp only [Q]; omega
  have hdQ : Qd ≤ Q := by dsimp only [Q]; omega
  let A := K+⌈A0⌉₊+⌈B0⌉₊+1
  have hAA : A0 ≤ (A : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show ⌈A0⌉₊ ≤ A by dsimp only [A]; omega))
  have hBA : B0 ≤ (A : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show ⌈B0⌉₊ ≤ A by dsimp only [A]; omega))
  have hKA : K ≤ A := by dsimp only [A]; omega
  refine ⟨A,Q,S,T,by dsimp only [A]; omega,by dsimp only [Q]; omega,hS,hT,ρ,hρ,C,?_⟩
  intro p hp N hTN F hF hlarge hmean
  have hN : 0 < N := hT.trans_le hTN
  obtain ⟨χ,hχC,hHor,hNorm,M,hM,hMS,hQM,hQB,hPM,hPB,b,hb,_,hζ,V,hV,hsize,hUseful⟩ :=
    hData p hp N hTN F hF hlarge hmean
  have hsize' : min ρ 1*(N : ℝ) ≤ V.card :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg N)).trans hsize
  rcases hAlternative p hp χ M b hζ N hN V hsize'
    (fun h hh => ⟨(hUseful h hh).2.1,(hUseful h hh).2.2.2⟩) with hcoeff | hvector
  · obtain ⟨r,hr,hrR,hBounds⟩ := hcoeff
    by_cases hnonzero : ∃ i, (nativeRationalIntegralCommutatorCharacter D L χ hHor.2.1 i).toLinearMap ≠ 0
    · obtain ⟨i,hne⟩ := hnonzero
      have hMS' : r*M ≤ R*S := Nat.mul_le_mul hrR hMS
      have he : nativeRationalCompactBracketCoefficient D L p χ (r*M) i =
          (r : ℝ)*nativeRationalCompactBracketCoefficient D L p χ M i := by
        dsimp only [nativeRationalCompactBracketCoefficient]
        push_cast
        ring
      have hsmall : (N : ℝ)*‖(nativeRationalCompactBracketCoefficient D L p χ (r*M) i : UnitAddCircle)‖ ≤ (R : ℝ) := by
        rw [he]
        exact hBounds i
      obtain ⟨f,hOriginal,hNormF,_,hMono,hBin⟩ :=
        hCommutator p hp N hN χ hχC hHor (r*M) (Nat.mul_pos hr hM) hMS' i hne hsmall
      have hNormQ := hNormF.trans (by exact_mod_cast hcQ : (Qc : ℝ) ≤ Q)
      exact Or.inl ⟨f,hOriginal,hNormQ,
        rough_native_norm_bounded_horizontal_grid_mem D.Γ _ (Nat.cast_nonneg Q) f hNormQ hOriginal,
        fun J hJ => (hMono J hJ).trans (by exact_mod_cast hcQ),
        fun J hJ => (hBin J hJ).trans (by exact_mod_cast hcQ)⟩
    · have hzero : ∀ i, (nativeRationalIntegralCommutatorCharacter D L χ hHor.2.1 i).toLinearMap = 0 := by
        intro i
        by_contra hn
        exact hnonzero ⟨i,hn⟩
      by_cases hDiff : nativeRationalRelativeDifferenceCharacter D L χ = 0
      · obtain ⟨h,hh⟩ := hV
        obtain ⟨f,hOriginal,hNormF,_,hMono,hBin⟩ :=
          hDiagonal p hp h χ hHor hNorm hDiff N hN (hUseful h hh).2.2.1
        have hNormQ := hNormF.trans (by exact_mod_cast hdQ : (Qd : ℝ) ≤ Q)
        exact Or.inl ⟨f,hOriginal,hNormQ,
          rough_native_norm_bounded_horizontal_grid_mem D.Γ _ (Nat.cast_nonneg Q) f hNormQ hOriginal,
          fun J hJ => (hMono J hJ).trans (by exact_mod_cast hdQ),
          fun J hJ => (hBin J hJ).trans (by exact_mod_cast hdQ)⟩
      · apply Or.inr
        refine ⟨χ,hχC,hHor,hNorm.trans hAA,M,hM,hMS,
          fun j hj hjL => (hQM j hj hjL).trans hBA,fun j hj hjL => (hQB j hj hjL).trans hBA,
          fun j hj hjL => (hPM j hj hjL).trans hBA,fun j hj hjL => (hPB j hj hjL).trans hBA,
          b,fun i => (hb i).trans (by exact_mod_cast hKA),hDiff,hzero,
          native_rational_integral_commutator_characters_zero_pairing D L χ hHor.2.1 hzero,V,hV,hsize,?_⟩
        intro h hh
        obtain ⟨hpos,hlt,hCoeff,hBracket⟩ := hUseful h hh
        exact ⟨hpos,hlt,⟨fun J hJ hJL => (hCoeff.1 J hJ hJL).trans hBA,
          fun J hJ hJL => (hCoeff.2 J hJ hJL).trans hBA⟩,hBracket.trans hBA⟩
  · obtain ⟨v,hv,hsizeV,hphase⟩ := hvector
    have hvi : ∀ i, |(v i : ℝ)| ≤ (R : ℝ) := by
      intro i
      have hn := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hsizeV
      have hr : ((v i).natAbs : ℝ) ≤ R := by exact_mod_cast hn
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hr
    obtain ⟨f,hOriginal,hNormF,_,hMono,hBin⟩ := hVector p hp N hN v hv hvi hphase
    have hNormQ := hNormF.trans (by exact_mod_cast hvQ : (Qv : ℝ) ≤ Q)
    exact Or.inl ⟨f,hOriginal,hNormQ,
      rough_native_norm_bounded_horizontal_grid_mem D.Γ _ (Nat.cast_nonneg Q) f hNormQ hOriginal,
      fun J hJ => (hMono J hJ).trans (by exact_mod_cast hvQ),
      fun J hJ => (hBin J hJ).trans (by exact_mod_cast hvQ)⟩

end Hindman168
