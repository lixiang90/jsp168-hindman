from pathlib import Path

old = Path('Hindman168/NativeRationalDenseFractionalPaperSeparation.lean').read_text(encoding='utf-8')
start = old.index('theorem native_rational_dense_fractional_paper_separation')
head = old[start:old.index(' := by',start)]
head = head.replace('native_rational_dense_fractional_paper_separation','native_rational_dense_bracket_first_alternative',1)
front = head[:head.index('    ∃ A B ρ H Z : ℝ,')]
packet = head[head.index('        ∃ χ ∈ C,'):head.index('            ∃ b : NativeRationalFirstLayerIndex')]
packet = packet.replace('‖χ‖ ≤ A','‖χ‖ ≤ (A : ℝ)').replace('≤ B)','≤ (A : ℝ))')
output = '''    ∃ A S T : ℕ, 0 < A ∧ 0 < S ∧ 0 < T ∧
      ∃ C : Finset ((nativeRationalRelativeData D L 1).E →L[ℝ] ℝ),
      ∀ (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
        (N : ℕ), T ≤ N → ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
        4 ≤ δ^2*(N : ℝ) →
        δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n =>
          nativeRationalTerminalFourierProjection D L k F (nativeMvPolynomialOrbit D p (fun _ => n)))‖ →
'''
end = '''            ∃ b : NativeRationalFirstLayerIndex D L → ℤ,
              (∀ i, |(b i : ℝ)| ≤ (A : ℝ)) ∧
              ((∀ i, (N : ℝ)*‖(nativeRationalCompactBracketCoefficient D L p χ M i : UnitAddCircle)‖ ≤ (A : ℝ)) ∨
                ∃ (v : NativeRationalFirstLayerIndex D L → ℤ) (r : ℤ), (v ≠ 0 ∨ r ≠ 0) ∧
                  (∑ i, (v i).natAbs)+r.natAbs ≤ A ∧
                  (N : ℝ)*‖(((∑ i, (v i : ℝ)*nativeRationalCompactBracketFrequency D L p i)+
                    (r : ℝ)*nativeRationalCompactBracketAlpha D L p hp χ M : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).E := borel (nativeRationalDegreeReducedData D L).E
  letI : MeasurableSpace (nativeRationalDegreeReducedData D L).G := borel (nativeRationalDegreeReducedData D L).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨A0,B0,ρ,_,Z,S,T,hA0,hB0,hρ,_,_,hS,hT,K,C,hData⟩ :=
    native_rational_dense_fractional_paper_separation D L hdeg hInverse k hk δ hδ hδ1
  obtain ⟨Q,_,hfirst⟩ := native_rational_bracket_first_alternative D L Z (min ρ 1) B0
    (lt_min hρ zero_lt_one) (min_le_right _ _) hB0.le
  let A := Q+K+⌈A0⌉₊+⌈B0⌉₊+1
  have hQA : Q ≤ A := by dsimp only [A]; omega
  have hKA : K ≤ A := by dsimp only [A]; omega
  have hAA : A0 ≤ (A : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show ⌈A0⌉₊ ≤ A by dsimp only [A]; omega))
  have hBA : B0 ≤ (A : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show ⌈B0⌉₊ ≤ A by dsimp only [A]; omega))
  refine ⟨A,S,T,by dsimp only [A]; omega,hS,hT,C,?_⟩
  intro p hp N hTN F hF hlarge hmean
  have hN : 0 < N := hT.trans_le hTN
  obtain ⟨χ,hχ,hHor,hNorm,M,hM,hMS,hQM,hQB,hPM,hPB,b,hb,_,hζ,V,_,hsize,hUseful⟩ :=
    hData p hp N hTN F hF hlarge hmean
  have hsize' : min ρ 1*(N : ℝ) ≤ V.card :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg N)).trans hsize
  have halt := hfirst p hp χ M b hζ N hN V hsize'
    (fun h hh => ⟨(hUseful h hh).2.1,(hUseful h hh).2.2.2⟩)
  refine ⟨χ,hχ,hHor,hNorm.trans hAA,M,hM,hMS,
    fun j hj hjL => (hQM j hj hjL).trans hBA,fun j hj hjL => (hQB j hj hjL).trans hBA,
    fun j hj hjL => (hPM j hj hjL).trans hBA,fun j hj hjL => (hPB j hj hjL).trans hBA,
    b,fun i => (hb i).trans (by exact_mod_cast hKA),?_⟩
  rcases halt with hcoeff | hmixed
  · exact Or.inl (fun i => (hcoeff i).trans (by exact_mod_cast hQA))
  · obtain ⟨v,r,hne,hbudget,hbound⟩ := hmixed
    exact Or.inr ⟨v,r,hne,hbudget.trans hQA,hbound.trans (by exact_mod_cast hQA)⟩

end Hindman168
'''
prefix = '''import Hindman168.NativeRationalBracketFirstAlternative

/-! GENUINE FIRST mixed-frequency alternative from SAME original nonzero
Fourier signal, preserving actual relative character, common natural M,
BOTH original higher P/Q tables and fixed budgets before all source inputs.
The full SECOND Claim 7.7 alternative remains open. -/
namespace Hindman168
open MeasureTheory Polynomial
open scoped Manifold ContDiff BigOperators
universe u

'''
Path('Hindman168/NativeRationalDenseBracketFirstAlternative.lean').write_text(prefix+front+output+packet+end,encoding='utf-8')
print('Wrote actual Fourier-signal first mixed alternative module.')
