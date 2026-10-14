from pathlib import Path

src=Path('Hindman168/NativeRationalDenseCommutatorAlternative.lean').read_text(encoding='utf-8')
header=src[:src.index(' := by')]
end_imports=header.index('\n\n/-!')
header='import Hindman168.NativeRationalDenseCommutatorAlternative\nimport Hindman168.NativeRationalNonlinearityExactFactorization'+header[end_imports:]
header=header.replace('native_rational_dense_commutator_alternative','native_rational_dense_nonlinearity_factorization')
header=header.replace('universe u\n','universe u\nattribute [local instance] lieGroup_smooth_min_three\n')
start=header.index('/-!')
end=header.index('-/',start)+2
header=header[:start]+'''/-! SAME actual Fourier signal yields FULL original inverse OR a genuine
smaller rational filtration with STRICTLY smaller nonlinearity AND an
ACTUAL exact source factorization. Removed factor may be UNBOUNDED;
small/rational splitting and correlation transfer remain open. -/'''+header[end:]
factor='''              ∃ K : NativeRationalLieFiltration D ℓ,
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
'''
needle='              ∃ V : Finset ℕ'
assert header.count(needle)==1
header=header.replace(needle,factor+'              ∃ V : Finset ℕ')
body=''' := by
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
'''
Path('Hindman168/NativeRationalDenseNonlinearityFactorization.lean').write_text(header+body,encoding='utf-8')
degree=header.replace('native_rational_dense_nonlinearity_factorization','native_rational_degree_two_dense_nonlinearity_factorization').replace('{s ℓ : ℕ}','{s : ℕ}')
end_imports=degree.index('\n\n/-!')
degree='import Hindman168.NativeRationalDenseNonlinearityFactorization'+degree[end_imports:]
start=degree.index(' (L : NativeRationalLieFiltration')
end=degree.index('    (k :',start)
degree=degree[:start]+' (L : NativeRationalLieFiltration D 2)\n'+degree[end:]
degree=degree.replace('ℓ','2')
body_two=''' := by
  exact native_rational_dense_nonlinearity_factorization D L (by omega)
    (native_rational_weighted_inverse_degree_one (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit) k hk δ hδ hδ1

end Hindman168
'''
Path('Hindman168/NativeRationalDegreeTwoDenseNonlinearityFactorization.lean').write_text(degree+body_two,encoding='utf-8')
