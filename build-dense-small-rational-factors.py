from pathlib import Path

src=Path('Hindman168/NativeRationalDenseNonlinearityFactorization.lean').read_text(encoding='utf-8')
header=src[:src.index(' := by')]
header=header.replace('import Hindman168.NativeRationalDenseCommutatorAlternative',
    'import Hindman168.NativeRationalDenseNonlinearityFactorization')
header=header.replace('import Hindman168.NativeRationalNonlinearityExactFactorization',
    'import Hindman168.NativeRationalNonlinearityExactFactorization\nimport Hindman168.NativeRationalZeroPairingCompleteTables\nimport Hindman168.NativeRationalNonlinearSmallRationalFactors')
header=header.replace('native_rational_dense_nonlinearity_factorization','native_rational_dense_small_rational_factors')
a=header.index('/-!'); b=header.index('-/',a)+2
header=header[:a]+'''/-! SAME original Fourier signal yields FULL original inverse OR genuine
smaller nonlinearity, COMPLETE native nonlinear tables and ACTUAL small /
rational factors, finite original lattice residues and error variation.
No large child correlation or arbitrary right-quotient action is assumed. -/'''+header[b:]
header=header.replace('3 ≤ j → j ≤ ℓ','2 ≤ j → j ≤ ℓ')
needle='            ∃ b : NativeRationalFirstLayerIndex D L → ℤ,'
header=header.replace(needle,'''            ((N : ℝ)*‖(((M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).eval 1 : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∧
'''+needle)
factor=Path('Hindman168/NativeRationalNonlinearSmallRationalFactors.lean').read_text(encoding='utf-8')
factor=factor[factor.index('theorem native_rational_nonlinear_small_rational_factors'):]
factor=factor[factor.index('    ∃ (z : ℕ → ℤ)'):factor.index(' := by')]
factor=factor.strip().replace('≤ B','≤ (A : ℝ)').replace('^2*B','^2*(A : ℝ)')
needle='                  ∀ (p0 : RoughVectorMvPolynomial Unit D.E)'
assert header.count(needle)==1
header=header.replace(needle,'                  ('+factor+') ∧\n'+needle)
body=''' := by
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
'''
Path('Hindman168/NativeRationalDenseSmallRationalFactors.lean').write_text(header+body,encoding='utf-8')
degree=header.replace('native_rational_dense_small_rational_factors','native_rational_degree_two_dense_small_rational_factors').replace('{s ℓ : ℕ}','{s : ℕ}')
end_imports=degree.index('\n\n/-!')
degree='import Hindman168.NativeRationalDenseSmallRationalFactors'+degree[end_imports:]
start=degree.index(' (L : NativeRationalLieFiltration'); end=degree.index('    (k :',start)
degree=degree[:start]+' (L : NativeRationalLieFiltration D 2)\n'+degree[end:]
degree=degree.replace('ℓ','2')
body_two=''' := by
  exact native_rational_dense_small_rational_factors D L (by omega)
    (native_rational_weighted_inverse_degree_one (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit) k hk δ hδ hδ1

end Hindman168
'''
Path('Hindman168/NativeRationalDegreeTwoDenseSmallRationalFactors.lean').write_text(degree+body_two,encoding='utf-8')
