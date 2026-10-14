from pathlib import Path

src = Path('Hindman168/NativeRationalDenseBracketOriginalDischarge.lean').read_text(encoding='utf-8')
header = src[:src.index(' := by')]
header = header.replace('import Hindman168.NativeRationalDenseBracketFullAlternative\nimport Hindman168.NativeRationalFirstLayerInverseReconstruction', '''import Hindman168.NativeRationalBracketFullAlternative
import Hindman168.NativeRationalFirstLayerInverseReconstruction
import Hindman168.NativeRationalCommutatorInverseReconstruction
import Hindman168.NativeRationalZeroCommutatorCharacters
import Hindman168.NativeRationalPureDiagonalInverseReconstruction''')
header = header.replace('native_rational_dense_bracket_original_discharge', 'native_rational_dense_commutator_alternative')
start = header.index('/-!')
end = header.index('-/',start)+2
header = header[:start]+'''/-! SAME actual Fourier signal yields FULL original inverse OR a NONZERO
actual F_2 difference character with vanishing commutator pairing. BOTH
higher P/Q tables AND actual dense relative/bracket sample bounds survive.
The remaining nonlinearity filtration/factorization is NOT assumed solved. -/'''+header[end:]
header = header.replace('      ∃ C : Finset', '      ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : Finset')
start = header.index('              ∃ r : ℕ')
header = header[:start]+'''              nativeRationalRelativeDifferenceCharacter D L χ ≠ 0 ∧
              (∀ i, (nativeRationalIntegralCommutatorCharacter D L χ
                (native_rational_horizontal_grid_relative_dummy) i).toLinearMap = 0) ∧
              (∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h = 0) ∧
              ∃ V : Finset ℕ, V.Nonempty ∧ ρ*(N : ℝ) ≤ V.card ∧
                ∀ h ∈ V, 0 < h ∧ h < N ∧ NativeRationalRelativeCoefficientBounds D L p hp h χ N (A : ℝ) ∧
                  (N : ℝ)*‖((scalarFractionalBracket
                    (nativeRationalCompactBracketBeta D L p χ M b) (nativeRationalCompactBracketAlpha D L p hp χ M)
                    (nativeRationalCompactBracketCoefficient D L p χ M) (nativeRationalCompactBracketFrequency D L p)
                    (h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ))'''
# The relative horizontal proof is explicitly bound, not supplied as an oracle.
needle = '''          RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
            (nativeRationalRelativeData D L 1).Γ χ.toLinearMap ∧ ‖χ‖ ≤ (A : ℝ) ∧'''
assert header.count(needle)==1
header = header.replace(needle,'''          ∃ hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
            (nativeRationalRelativeData D L 1).Γ χ.toLinearMap, ‖χ‖ ≤ (A : ℝ) ∧''')
header = header.replace('(native_rational_horizontal_grid_relative_dummy)', 'hHor.2.1')
body = ''' := by
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
'''
Path('Hindman168/NativeRationalDenseCommutatorAlternative.lean').write_text(header+body,encoding='utf-8')
degree = header.replace('native_rational_dense_commutator_alternative', 'native_rational_degree_two_dense_commutator_alternative').replace('{s ℓ : ℕ}', '{s : ℕ}')
end_imports = degree.index('\n\n/-!')
degree = 'import Hindman168.NativeRationalDenseCommutatorAlternative'+degree[end_imports:]
start = degree.index(' (L : NativeRationalLieFiltration')
end = degree.index('    (k :',start)
degree = degree[:start]+' (L : NativeRationalLieFiltration D 2)\n'+degree[end:]
degree = degree.replace('ℓ','2')
body_two = ''' := by
  exact native_rational_dense_commutator_alternative D L (by omega)
    (native_rational_weighted_inverse_degree_one (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit) k hk δ hδ hδ1

end Hindman168
'''
Path('Hindman168/NativeRationalDegreeTwoDenseCommutatorAlternative.lean').write_text(degree+body_two,encoding='utf-8')
