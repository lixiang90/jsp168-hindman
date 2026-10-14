from pathlib import Path

src=Path('Hindman168/NativeRationalDenseRightFactors.lean').read_text(encoding='utf-8')
header=src[:src.index(' := by')]
header=header[header.index('\n\n/-!'):]
header='import Hindman168.NativeRationalDenseRightFactors\nimport Hindman168.NativeRationalFiniteCharacterChildBudget'+header
header=header.replace('native_rational_dense_right_factors','native_rational_dense_child_signal')
a=header.index('/-!'); b=header.index('-/',a)+2
header=header[:a]+'''/-! SAME original Fourier signal now yields FULL original inverse OR
GENUINE constructed smaller-source child UNIT discrepancy with UNIFORM
finite-character geometry/budgets and original-scale length. ALL previous
right-factor/dense/table data are retained. No child inverse is assumed. -/'''+header[b:]
needle='''      ∀ (p : RoughVectorMvPolynomial Unit D.E)'''
assert header.count(needle)==1
header=header.replace(needle,'''      ∃ B : ℕ, 0 < B ∧ ∃ θ : ℝ, 0 < θ ∧
      (∀ χ ∈ C, NativeRationalNonlinearityCharacterGood D L χ →
        NativeRationalCharacterChildBudget D L k (A : ℝ) δ S χ B θ) ∧
'''+needle)
budget=Path('Hindman168/NativeRationalCharacterChildBudget.lean').read_text(encoding='utf-8')
a=budget.index('    ∃ hHor :',budget.index('def NativeRationalCharacterChildBudget'))
b=budget.index('\ntheorem native_rational_character_child_budget_exists',a)
budget=budget[a:b].strip()
a=budget.index('      ∀ M :'); b=budget.index('          ∃ (a : ℤ)',a)
app=budget[:a]+budget[b:]
app=app.replace('≤ A','≤ (A : ℝ)')
app=app.replace('let K0 := nativeRationalNonlinearKernelFiltration D L χ hHor hzero',
    'let K0 := nativeRationalNonlinearKernelFiltration D L χ hHor hzero')
needle='              ∃ V : Finset ℕ'
assert header.count(needle)==1
header=header.replace(needle,'              ('+app+') ∧\n'+needle)
body=''' := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A,Q,S,T0,hA,hQ,hS,hT0,ρ,hρ,C,hData⟩ :=
    native_rational_dense_right_factors D L hdeg hInverse k hk δ hδ hδ1
  obtain ⟨B,hB,θ,hθ,hBudgets⟩ := native_rational_finite_character_child_budget D L hdeg k hk
    (A : ℝ) δ S (Nat.cast_nonneg A) hδ hS C
  let T := T0+B+1
  refine ⟨A,Q,S,T,hA,hQ,hS,by dsimp only [T]; omega,ρ,hρ,C,B,hB,θ,hθ,hBudgets,?_⟩
  intro p hp N hTN F hF hlarge hSignal
  have hT0N : T0 ≤ N := (show T0 ≤ T by dsimp only [T]; omega).trans hTN
  have hBN : B ≤ N := (show B ≤ T by dsimp only [T]; omega).trans hTN
  rcases hData p hp N hT0N F hF hlarge hSignal with hOriginal | hRemaining
  · exact Or.inl hOriginal
  · obtain ⟨χ,hχC,hHor,hNorm,M,hM,hMS,hQM,hQB,hPM,hPB,hEval,b,hb,hDiff,hZero,hPair,
        K0,hLayers,hRank,hDrop,hGeom,V,hV,hsize,hUseful⟩ := hRemaining
    have hGood : NativeRationalNonlinearityCharacterGood D L χ := ⟨hHor,hPair,hDiff⟩
    obtain ⟨hHor2,hPair2,hDiff2,j2,y2,q2,K2,hj2,hjL,hy2,hyRat2,hFy2,hHigher2,hq2,hpow2,hK2,
        hqB,hKB,hyB,h4B,hSelect⟩ := hBudgets χ hχC hGood
    have hApp := hSelect M hM hMS p hp N hBN hQM F hF hSignal
    refine Or.inr ⟨χ,hχC,hHor,hNorm,M,hM,hMS,hQM,hQB,hPM,hPB,hEval,b,hb,hDiff,hZero,hPair,
      K0,hLayers,hRank,hDrop,hGeom,?_,V,hV,hsize,hUseful⟩
    exact ⟨hHor2,hPair2,hDiff2,j2,y2,q2,K2,hj2,hjL,hy2,hyRat2,hFy2,hHigher2,hq2,hpow2,hK2,
      hqB,hKB,hyB,h4B,hApp⟩

end Hindman168
'''
Path('Hindman168/NativeRationalDenseChildSignal.lean').write_text(header+body,encoding='utf-8')
degree=header.replace('native_rational_dense_child_signal','native_rational_degree_two_dense_child_signal').replace('{s ℓ : ℕ}','{s : ℕ}')
b=degree.index('\n\n/-!')
degree='import Hindman168.NativeRationalDenseChildSignal'+degree[b:]
a=degree.index(' (L : NativeRationalLieFiltration'); b=degree.index('    (k :',a)
degree=degree[:a]+' (L : NativeRationalLieFiltration D 2)\n'+degree[b:]
degree=degree.replace('ℓ','2')
body_two=''' := by
  exact native_rational_dense_child_signal D L (by omega)
    (native_rational_weighted_inverse_degree_one (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit) k hk δ hδ hδ1

end Hindman168
'''
Path('Hindman168/NativeRationalDegreeTwoDenseChildSignal.lean').write_text(degree+body_two,encoding='utf-8')
