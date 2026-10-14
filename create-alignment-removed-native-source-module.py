from pathlib import Path

source=Path('Hindman168/AlignmentExposedNativeSource.lean').read_text(encoding='utf-8')
header=source[source.index('namespace Hindman168'):source.index('noncomputable def alignmentExposedNativeSource')]
content='''import Hindman168.AlignmentExposedNativeSource
import Hindman168.RoughRemovedFactorPolynomial

/-! The actual exposed source with ONE factor free and all other factors
frozen. The native polynomial/log residual packet is constructed outright;
sample equality still refers to the original actual cube array. -/
'''+header+'''
noncomputable def alignmentRemovedNativePolynomial
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G) :
    RoughVectorMvPolynomial (Option (Option κ)) (alignmentNativeArrayData D n v hv).E :=
  roughRemovedFactorPolynomial j frozen
    (alignmentExposedNativeVectorPolynomial D n v hv b F q₀ w T x shift weight g a)

noncomputable def alignmentRemovedNativeSource
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G) :
    (Option (Option κ) → ℝ) → (alignmentNativeArrayData D n v hv).G :=
  nativeVectorPolynomialSource (alignmentNativeArrayData D n v hv)
    (alignmentRemovedNativePolynomial D n v hv b F q₀ w T x j frozen shift weight g a)

theorem alignment_removed_native_polynomial_degree
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G) :
    RoughVectorMvDegreeLE
      (alignmentRemovedNativePolynomial D n v hv b F q₀ w T x j frozen shift weight g a)
      (((s*s+1)^(s+1))*max 1 T.card) :=
  rough_removed_factor_polynomial_degree j frozen
    (alignment_exposed_native_vector_polynomial_degree D n v hv b F q₀ w T x shift weight g a)

theorem alignment_removed_native_source_frozen_update
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ) (z : ℝ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G) :
    alignmentRemovedNativeSource D n v hv b F q₀ w T x j (Function.update frozen j z) shift weight g a =
      alignmentRemovedNativeSource D n v hv b F q₀ w T x j frozen shift weight g a := by
  unfold alignmentRemovedNativeSource alignmentRemovedNativePolynomial
  rw [rough_removed_factor_polynomial_frozen_update]

theorem alignment_removed_native_residual_packet
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G)
    (residue : Option κ → ℤ) (q : ℕ) :
    let p := alignmentRemovedNativePolynomial D n v hv b F q₀ w T x j frozen shift weight g a
    let Q := alignmentRemovedNativeSource D n v hv b F q₀ w T x j frozen shift weight g a
    RoughVectorMvDegreeLE (roughNativeResidualPolynomial p residue q)
      (((s*s+1)^(s+1))*max 1 T.card) ∧
    ∀ (z : ℝ) (y : Option κ → ℝ),
      roughVectorMvEval (roughNativeResidualPolynomial p residue q) (Option.elim · z y) =
        nativeLieGlobalLogarithm (E := (alignmentNativeArrayData D n v hv).E)
          (I := (alignmentNativeArrayData D n v hv).I) (G := (alignmentNativeArrayData D n v hv).G)
          (roughNativeResidualSource (alignmentNativeArrayData D n v hv) Q residue q (Option.elim · z y)) := by
  dsimp only
  constructor
  · exact rough_native_residual_polynomial_degree
      (alignment_removed_native_polynomial_degree D n v hv b F q₀ w T x j frozen shift weight g a) residue q
  · exact native_vector_polynomial_residual_log (alignmentNativeArrayData D n v hv) _ residue q

'''
sample=source[source.index('theorem alignment_exposed_native_source_actual_sample'):]
sample=sample[:sample.index(' := by')]
sample=sample.replace('alignment_exposed_native_source_actual_sample','alignment_removed_native_source_actual_sample')
sample=sample.replace('    (T : Finset (Fin N)) (hT :','    (j : Fin N) (T : Finset (Fin N)) (hT :')
sample=sample.replace('    let z := Sum.elim','    let z :=')
sample=sample.replace(')) (fun j : Fin N => (y j : ℝ))', '))')
sample=sample.replace('    alignmentExposedNativeSource D n v hv b F q₀ w T x shift weight g a z=actual',
 '''    alignmentRemovedNativeSource D n v hv b F q₀ w T x j (fun k => (y k : ℝ)) shift weight g a
      (Option.elim · (y j : ℝ) z)=actual''')
content+=sample+''' := by
  dsimp only
  apply native_vector_polynomial_source_sample
  rw [alignmentRemovedNativePolynomial,rough_removed_factor_polynomial_eval,Function.update_eq_self]
  exact alignment_exposed_native_vector_polynomial_actual_eval D n v hv b
    hF hq hw T hT hx hy hkey p ell hp inc weight shift g a

end Hindman168
'''
Path('Hindman168/AlignmentRemovedFactorNativeSource.lean').write_text(content,encoding='utf-8')
print('Created actual one-factor native source and genuine residual packet.')
