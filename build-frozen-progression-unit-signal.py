from pathlib import Path

src=Path('Hindman168/NativeRationalFrozenProgressionMean.lean').read_text(encoding='utf-8')
header=src[:src.index(' := by')]
header=header[header.index('\n\n/-!'):]
header='''import Hindman168.NativeRationalFrozenProgressionMean
import Hindman168.NativeRationalFiniteResidueUnitDetection
import Hindman168.NativeUnitCubePolynomialDiscrepancy'''+header
header=header.replace('native_rational_frozen_progression_mean','native_rational_frozen_progression_unit_signal')
a=header.index('/-!'); b=header.index('-/',a)+2
header=header[:a]+'''/-! ACTUAL original Fourier signal and genuine right factors yield a
TRUE smaller-filtration polynomial on standard child cube with LARGE
UNIT-observable canonical discrepancy. One positive threshold precedes
ALL bounded denominators/raw sources/N. No child inverse is assumed. -/'''+header[b:]
header=header.replace('    (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) :',
'''    (A δ : ℝ) (S q : ℕ) (hA : 0 ≤ A) (hδ : 0 < δ) (hS : 0 < S) (hq : 0 < q)
    (hpow : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ) :''')
header=header.replace('''    ∃ K : ℕ, 0 < K ∧ ∀ (M q N : ℕ), 0 < M → 0 < q → 4*K*(M*q) ≤ N →
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ →''',
'''    ∃ K : ℕ, 0 < K ∧ ∃ θ : ℝ, 0 < θ ∧ ∀ (M N : ℕ), 0 < M → M ≤ S → 4*K*(M*q) ≤ N →''')
header+=''' ∧
              ∃ J ∈ unitLipschitzObservables (D.G ⧸ roughConjugateSubgroup D.Γ ρ),
                θ < ‖nativeNilmanifoldFiniteDiscrepancy Dm (scalarMvIntegerCube Unit T) (nativeMvPolynomialOrbit Dm pNew) J‖'''
body=''' := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨K,hK,hSelect⟩ := native_rational_frozen_progression_mean D L K0 hDrop k hk y hyRat j A δ hA hδ
  obtain ⟨θ,hθ,hDetect⟩ := native_rational_finite_residue_unit_detection D L k hk y
    (((j+1 : ℕ) : ℝ)^2*A) (δ/2) S q (by positivity) hS hq
  refine ⟨K,hK,θ,hθ,?_⟩
  intro M N hM hMS hLarge z E p pK hED h0 h1 hBounds hpK hpKD hExact F hF hSignal
  obtain ⟨a,T,m,c,ha0,haN,hT,hm,hLength,hC,pNew,hWeights,hDegree,hDropNew,hOrbit,hZero,hMean⟩ :=
    hSelect M q N hM hq hLarge hpow z E p pK hED h0 h1 hBounds hpK hpKD hExact F hF hSignal
  let ρ := nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y)
  let Dm := nativeConjugateNilmanifoldData D ρ
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := Dm.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨J,hJ,hUnit⟩ := hDetect M hM hMS m hm (Finset.Ico 0 (T : ℤ))
    (fun n => nativeMvPolynomialOrbit Dm pNew (fun _ => n)) c hC F hF hMean.le
  refine ⟨a,T,m,c,ha0,haN,hT,hm,hLength,hC,pNew,hWeights,hDegree,hDropNew,hOrbit,hZero,hMean,J,hJ,?_⟩
  have hCube := native_unit_cube_polynomial_discrepancy Dm pNew T J
  exact hUnit.trans_eq (congrArg norm hCube.symm)

end Hindman168
'''
Path('Hindman168/NativeRationalFrozenProgressionUnitSignal.lean').write_text(header+body,encoding='utf-8')
