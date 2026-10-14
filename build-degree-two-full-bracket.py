from pathlib import Path

src = Path('Hindman168/NativeRationalDenseBracketFullAlternative.lean').read_text(encoding='utf-8')
header = src[:src.index(' := by')]
header = header.replace('import Hindman168.NativeRationalBracketFullAlternative', 'import Hindman168.NativeRationalDenseBracketFullAlternative')
header = header.replace('native_rational_dense_bracket_full_alternative', 'native_rational_degree_two_dense_bracket_full_alternative')
header = header.replace('{s ℓ : ℕ}', '{s : ℕ}')
start = header.index(' (L : NativeRationalLieFiltration')
end = header.index('    (k :', start)
header = header[:start] + ' (L : NativeRationalLieFiltration D 2)\n' + header[end:]
header = header.replace('ℓ', '2')
body = ''' := by
  exact native_rational_dense_bracket_full_alternative D L (by omega)
    (native_rational_weighted_inverse_degree_one (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit) k hk δ hδ hδ1

end Hindman168
'''
Path('Hindman168/NativeRationalDegreeTwoDenseBracketFullAlternative.lean').write_text(header+body, encoding='utf-8')
