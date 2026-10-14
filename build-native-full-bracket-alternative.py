from pathlib import Path

source = Path('Hindman168/NativeRationalBracketFirstAlternative.lean').read_text(encoding='utf-8')
source = source.replace('Hindman168.ScalarFractionalBracketFirstAlternative','Hindman168.ScalarFractionalBracketFullAlternative')
source = source.replace('native_rational_bracket_first_alternative','native_rational_bracket_full_alternative')
source = source.replace('scalar_fractional_bracket_first_alternative','scalar_fractional_bracket_full_alternative')
source = source.replace('(Z δ B : ℝ) (hδ : 0 < δ)', '(Z δ B : ℝ) (hZ : 0 ≤ Z) (hδ : 0 < δ)')
source = source.replace('Z δ B hδ hδ1 hB','Z δ B hZ hδ hδ1 hB')
start = source.index('        (∀ i, (N : ℝ)*‖(nativeRationalCompactBracketCoefficient')
end = source.index(' := by',start)
conclusion = '''        (∃ r : ℕ, 0 < r ∧ r ≤ A ∧ ∀ i,
          (N : ℝ)*‖(((r : ℝ)*nativeRationalCompactBracketCoefficient D L p χ M i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∨
          ∃ k : NativeRationalFirstLayerIndex D L → ℤ, k ≠ 0 ∧ (∑ i, (k i).natAbs) ≤ A ∧
            (N : ℝ)*‖((∑ i, (k i : ℝ)*nativeRationalCompactBracketFrequency D L p i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)'''
source = source[:start]+conclusion+source[end:]
a=source.index('/-!'); b=source.index('-/',a)
source=source[:a]+'''/-! GENUINE complete bracket alternative APPLIED to SAME native parameters
and actual useful shifts, with positive natural multiplier OR original
nonzero integer vector. No analytic inverse oracle is used. -/'''+source[b+2:]
Path('Hindman168/NativeRationalBracketFullAlternative.lean').write_text(source,encoding='utf-8')

source = Path('Hindman168/NativeRationalDenseBracketFirstAlternative.lean').read_text(encoding='utf-8')
source=source.replace('Hindman168.NativeRationalBracketFirstAlternative','Hindman168.NativeRationalBracketFullAlternative')
source=source.replace('native_rational_dense_bracket_first_alternative','native_rational_dense_bracket_full_alternative')
source=source.replace('native_rational_bracket_first_alternative','native_rational_bracket_full_alternative')
source=source.replace('A0,B0,ρ,_,Z,S,T,hA0,hB0,hρ,_,_,hS,hT','A0,B0,ρ,_,Z,S,T,hA0,hB0,hρ,_,hZ,hS,hT')
source=source.replace('D L Z (min ρ 1) B0\n','D L Z (min ρ 1) B0 hZ\n')
start=source.index('              ((∀ i, (N : ℝ)*‖(nativeRationalCompactBracketCoefficient')
end=source.index(' := by',start)
conclusion='''              ((∃ r : ℕ, 0 < r ∧ r ≤ A ∧ ∀ i,
                (N : ℝ)*‖(((r : ℝ)*nativeRationalCompactBracketCoefficient D L p χ M i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∨
                ∃ v : NativeRationalFirstLayerIndex D L → ℤ, v ≠ 0 ∧ (∑ i, (v i).natAbs) ≤ A ∧
                  (N : ℝ)*‖((∑ i, (v i : ℝ)*nativeRationalCompactBracketFrequency D L p i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ))'''
source=source[:start]+conclusion+source[end:]
start=source.index('  rcases halt with ')
source=source[:start]+'''  rcases halt with hcoeff | hdot
  · obtain ⟨r,hr,hrQ,hBounds⟩ := hcoeff
    exact Or.inl ⟨r,hr,hrQ.trans hQA,fun i => (hBounds i).trans (by exact_mod_cast hQA)⟩
  · obtain ⟨v,hne,hsize,hbound⟩ := hdot
    exact Or.inr ⟨v,hne,hsize.trans hQA,hbound.trans (by exact_mod_cast hQA)⟩

end Hindman168
'''
a=source.index('/-!'); b=source.index('-/',a)
source=source[:a]+'''/-! GENUINE FULL fixed-data Claim 7.7 alternative from SAME original Fourier
signal, preserving relative character, common natural M, BOTH higher P/Q
tables and geometry-only budgets before all raw sources. Original inverse
case-(i) character/reducible-filtration reconstruction remains open. -/'''+source[b+2:]
Path('Hindman168/NativeRationalDenseBracketFullAlternative.lean').write_text(source,encoding='utf-8')
print('Wrote actual native packet and Fourier signal FULL bracket applications.')
