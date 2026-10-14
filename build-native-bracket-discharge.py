from pathlib import Path

src = Path('Hindman168/NativeRationalDenseBracketFullAlternative.lean').read_text(encoding='utf-8')
header = src[:src.index(' := by')]
header = header.replace('import Hindman168.NativeRationalBracketFullAlternative', 'import Hindman168.NativeRationalDenseBracketFullAlternative\nimport Hindman168.NativeRationalFirstLayerInverseReconstruction')
header = header.replace('native_rational_dense_bracket_full_alternative', 'native_rational_dense_bracket_original_discharge')
header = header.replace('∃ A S T : ℕ, 0 < A ∧ 0 < S ∧ 0 < T ∧', '∃ A Q S T : ℕ, 0 < A ∧ 0 < Q ∧ 0 < S ∧ 0 < T ∧')
rec = Path('Hindman168/NativeRationalFirstLayerInverseReconstruction.lean').read_text(encoding='utf-8')
original = rec[rec.index('          ∃ χ : D.E'):rec.index(' := by')].strip()
start = header.index('        ∃ χ ∈ C,')
relative = header[start:].strip()
start_tail = relative.index('              ((∃ r : ℕ')
relative = relative[:start_tail] + '''              ∃ r : ℕ, 0 < r ∧ r ≤ A ∧ ∀ i,
                (N : ℝ)*‖(((r : ℝ)*nativeRationalCompactBracketCoefficient D L p χ M i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)'''
header = header[:start] + '        (' + original + ') ∨\n        (' + relative + ')'
body = ''' := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A,S,T,hA,hS,hT,C,hfull⟩ :=
    native_rational_dense_bracket_full_alternative D L hdeg hInverse k hk δ hδ hδ1
  obtain ⟨Q,hQ,hreconstruct⟩ := native_rational_first_layer_inverse_reconstruction D L
    (A : ℝ) (A : ℝ) (Nat.cast_nonneg A) (Nat.cast_nonneg A)
  refine ⟨A,Q,S,T,hA,hQ,hS,hT,C,?_⟩
  intro p hp N hTN F hF hlarge hmean
  obtain ⟨χ,hχ,hhor,hnorm,M,hM,hMS,hQM,hQB,hPM,hPB,b,hb,halt⟩ :=
    hfull p hp N hTN F hF hlarge hmean
  rcases halt with hcoeff | hvector
  · exact Or.inr ⟨χ,hχ,hhor,hnorm,M,hM,hMS,hQM,hQB,hPM,hPB,b,hb,hcoeff⟩
  · obtain ⟨v,hv,hsize,hphase⟩ := hvector
    have hvi : ∀ i, |(v i : ℝ)| ≤ (A : ℝ) := by
      intro i
      have hn := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hsize
      have hr : ((v i).natAbs : ℝ) ≤ A := by exact_mod_cast hn
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hr
    exact Or.inl (hreconstruct p hp N (hT.trans_le hTN) v hv hvi hphase)

end Hindman168
'''
Path('Hindman168/NativeRationalDenseBracketOriginalDischarge.lean').write_text(header+body, encoding='utf-8')

degree = header.replace('import Hindman168.NativeRationalDenseBracketFullAlternative\nimport Hindman168.NativeRationalFirstLayerInverseReconstruction', 'import Hindman168.NativeRationalDenseBracketOriginalDischarge')
degree = degree.replace('native_rational_dense_bracket_original_discharge', 'native_rational_degree_two_dense_bracket_original_discharge').replace('{s ℓ : ℕ}', '{s : ℕ}')
start = degree.index(' (L : NativeRationalLieFiltration')
end = degree.index('    (k :', start)
degree = degree[:start] + ' (L : NativeRationalLieFiltration D 2)\n' + degree[end:]
degree = degree.replace('ℓ', '2')
body_two = ''' := by
  exact native_rational_dense_bracket_original_discharge D L (by omega)
    (native_rational_weighted_inverse_degree_one (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit) k hk δ hδ hδ1

end Hindman168
'''
Path('Hindman168/NativeRationalDegreeTwoDenseBracketOriginalDischarge.lean').write_text(degree+body_two, encoding='utf-8')
