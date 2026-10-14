from pathlib import Path

source=Path('Hindman168/AlignmentExposedNativeVectorPolynomial.lean').read_text(encoding='utf-8')
header=source[source.index('namespace Hindman168'):source.index('noncomputable def alignmentExposedNativeVectorPolynomial')]
content='''import Hindman168.AlignmentExposedNativeVectorPolynomial

/-! The all-real native source constructed from the ACTUAL exposed vector
polynomial. Its values at genuine cube samples are proved equal to the
original group array, so extension values cannot replace the sampled source. -/
'''+header+'''
noncomputable def alignmentExposedNativeSource
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G) :
    (Sum (Option κ) (Fin N) → ℝ) → (alignmentNativeArrayData D n v hv).G :=
  nativeVectorPolynomialSource (alignmentNativeArrayData D n v hv)
    (alignmentExposedNativeVectorPolynomial D n v hv b F q₀ w T x shift weight g a)

theorem alignment_exposed_native_source_log
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G)
    (z : Sum (Option κ) (Fin N) → ℝ) :
    roughVectorMvEval (alignmentExposedNativeVectorPolynomial D n v hv b F q₀ w T x shift weight g a) z =
      nativeLieGlobalLogarithm (E := (alignmentNativeArrayData D n v hv).E)
        (I := (alignmentNativeArrayData D n v hv).I) (G := (alignmentNativeArrayData D n v hv).G)
        (alignmentExposedNativeSource D n v hv b F q₀ w T x shift weight g a z) :=
  (native_vector_polynomial_source_log (alignmentNativeArrayData D n v hv) _ z).symm

'''
sample=source[source.index('theorem alignment_exposed_native_vector_polynomial_actual_eval'):]
sample=sample[:sample.index(' := by')]
sample=sample.replace('alignment_exposed_native_vector_polynomial_actual_eval','alignment_exposed_native_source_actual_sample')
tail='''    alignmentExposedNativeSource D n v hv b F q₀ w T x shift weight g a z=actual'''
sample=sample[:sample.index('    roughVectorMvEval')]+tail
content+=sample+''' := by
  dsimp only
  apply native_vector_polynomial_source_sample
  exact alignment_exposed_native_vector_polynomial_actual_eval D n v hv b
    hF hq hw T hT hx hy hkey p ell hp inc weight shift g a

end Hindman168
'''
Path('Hindman168/AlignmentExposedNativeSource.lean').write_text(content,encoding='utf-8')
print('Created actual exposed native source with all-real and actual-sample identities.')
