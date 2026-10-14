from pathlib import Path

old = Path('Hindman168/NativeRationalDensePaperSeparation.lean').read_text(encoding='utf-8')
start = old.index('theorem native_rational_dense_paper_separation')
head = old[start:old.index(' := by',start)]
head = head.replace('native_rational_dense_paper_separation','native_rational_dense_fractional_paper_separation',1)
head = head.replace('∃ A B ρ : ℝ, ∃ S T : ℕ, 0 < A ∧ 0 < B ∧ 0 < ρ ∧ 0 < S ∧ 0 < T ∧',
    '∃ A B ρ H Z : ℝ, ∃ S T : ℕ, 0 < A ∧ 0 < B ∧ 0 < ρ ∧ 0 ≤ H ∧ 0 ≤ Z ∧ 0 < S ∧ 0 < T ∧\n      ∃ K : ℕ,')
tail = '''            ∃ b : NativeRationalFirstLayerIndex D L → ℤ,
              (∀ i, |(b i : ℝ)| ≤ (K : ℝ)) ∧
              (∀ i, |nativeRationalCompactBracketFrequency D L p i| ≤ H) ∧
              (∀ i, |nativeRationalCompactBracketCoefficient D L p χ M i| ≤ Z) ∧
              ∃ V : Finset ℕ, V.Nonempty ∧ ρ*(N : ℝ) ≤ V.card ∧
                ∀ h ∈ V, 0 < h ∧ h < N ∧ NativeRationalRelativeCoefficientBounds D L p hp h χ N B ∧
                  (N : ℝ)*‖((scalarFractionalBracket
                    (nativeRationalCompactBracketBeta D L p χ M b) (nativeRationalCompactBracketAlpha D L p hp χ M)
                    (nativeRationalCompactBracketCoefficient D L p χ M) (nativeRationalCompactBracketFrequency D L p)
                    (h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ B'''
head = head[:head.index('            ∃ U : Finset ℕ,')] + tail
body = ''' := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A,B,ρ,S,T,hA,hB,hρ,hS,hT,C,hData⟩ := native_rational_dense_paper_separation D L hdeg hInverse k hk δ hδ hδ1
  obtain ⟨ρ',hρ',K,hRefine⟩ := native_rational_dense_fractional_input D L ρ hρ
  obtain ⟨H,hH,hFrequency⟩ := native_rational_compact_bracket_frequency_bound D L
  obtain ⟨Z,hZ,hCoefficient⟩ := native_rational_compact_bracket_coefficient_bound D L A hA.le S
  refine ⟨A,B,ρ',H,Z,S,T,hA,hB,hρ',hH,hZ,hS,hT,K,C,?_⟩
  intro p hp N hTN F hF hlarge hmean
  obtain ⟨χ,hχ,hHor,hNorm,M,hM,hMS,hQM,hQB,hPM,hPB,U,hU,hsize,hUseful⟩ := hData p hp N hTN F hF hlarge hmean
  obtain ⟨b,hb,V,hVU,hV,hsizeV,hBracket⟩ := hRefine p hp χ hHor.2.1 M N B U hU hsize
    (fun h hh => (hUseful h hh).2.2.2)
  refine ⟨χ,hχ,hHor,hNorm,M,hM,hMS,hQM,hQB,hPM,hPB,b,hb,hFrequency p,
    hCoefficient p χ hNorm M hMS,V,hV,hsizeV,?_⟩
  intro h hh
  obtain ⟨hpos,hlt,hBounds,_⟩ := hUseful h (hVU hh)
  exact ⟨hpos,hlt,hBounds,hBracket h hh⟩

end Hindman168
'''
prefix = '''import Hindman168.NativeRationalDensePaperSeparation
import Hindman168.NativeRationalDenseFractionalInput

/-! Actual nonzero-frequency signal yields a bounded fractional bracket
input on SAME refined useful shifts, preserving BOTH higher P/Q tables,
the SAME bounded natural M, actual relative character and original scale.
The quantitative bracket alternative itself is not assumed or concluded. -/
namespace Hindman168
open MeasureTheory Polynomial
open scoped Manifold ContDiff BigOperators
universe u

'''
Path('Hindman168/NativeRationalDenseFractionalPaperSeparation.lean').write_text(prefix+head+body,encoding='utf-8')
print('Wrote actual dense fractional paper separation module.')
