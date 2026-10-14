from pathlib import Path

src=Path('Hindman168/NativeRationalDenseSmallRationalFactors.lean').read_text(encoding='utf-8')
header,body=src.split(' := by',1)
header=header[header.index('\n\n/-!'):]
header='import Hindman168.NativeRationalDenseSmallRationalFactors\nimport Hindman168.NativeRationalNonlinearRightFactors'+header
header=header.replace('native_rational_dense_small_rational_factors','native_rational_dense_right_factors')
a=header.index('/-!'); b=header.index('-/',a)+2
header=header[:a]+'''/-! SAME original Fourier signal now has ACTUAL right-ordered factors,
g=epsilon*gK_conjugated*gamma, with TRUE smaller-filtration source and
finite original-lattice representatives for ACTUAL full orbit samples.
Error is still variable; no frozen-observable child correlation is assumed. -/'''+header[b:]
right=Path('Hindman168/NativeRationalNonlinearRightFactors.lean').read_text(encoding='utf-8')
right=right[right.index('    ∃ (z : ℕ → ℤ)'):right.index(' := by')].strip()
right=right.replace('≤ B','≤ (A : ℝ)').replace('^2*B','^2*(A : ℝ)')
a=header.index('                  (∃ (z : ℕ → ℤ)'); b=header.index('                  ∀ (p0',a)
header=header[:a]+'                  ('+right+') ∧\n'+header[b:]
body=body.replace('native_rational_nonlinear_small_rational_factors','native_rational_nonlinear_right_factors')
body=body.replace('hExact,hVar,hValue,hResidues,hPeriod','hExact,hVar,hValue,hWhole,hResidues,hPeriod')
body=body.replace('hExact,hVarA,hValueA,hResidues,hPeriod','hExact,hVarA,hValueA,hWhole,hResidues,hPeriod')
Path('Hindman168/NativeRationalDenseRightFactors.lean').write_text(header+' := by'+body,encoding='utf-8')
degree=header.replace('native_rational_dense_right_factors','native_rational_degree_two_dense_right_factors').replace('{s ℓ : ℕ}','{s : ℕ}')
end_imports=degree.index('\n\n/-!')
degree='import Hindman168.NativeRationalDenseRightFactors'+degree[end_imports:]
a=degree.index(' (L : NativeRationalLieFiltration'); b=degree.index('    (k :',a)
degree=degree[:a]+' (L : NativeRationalLieFiltration D 2)\n'+degree[b:]
degree=degree.replace('ℓ','2')
body_two=''' := by
  exact native_rational_dense_right_factors D L (by omega)
    (native_rational_weighted_inverse_degree_one (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit) k hk δ hδ hδ1

end Hindman168
'''
Path('Hindman168/NativeRationalDegreeTwoDenseRightFactors.lean').write_text(degree+body_two,encoding='utf-8')
