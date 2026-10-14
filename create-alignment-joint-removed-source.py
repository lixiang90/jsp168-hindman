from pathlib import Path

source=Path('Hindman168/AlignmentJointExposedNativeSource.lean').read_text(encoding='utf-8')
header=source[source.index('namespace Hindman168'):source.index('noncomputable def alignmentJointExposedNativePolynomial')]
family='(fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))'
joint='nativeFinitePiData '+family
content='''import Hindman168.AlignmentJointExposedNativeSource
import Hindman168.RoughRemovedFactorPolynomial

/-! The genuine finite JOINT source with only the removed factor free.
All components and every spatial variable survive. Normalized residue
packets and ORIGINAL simultaneous sampled-array equality are proved. -/
'''+header+'''
noncomputable def alignmentJointRemovedNativePolynomial
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    RoughVectorMvPolynomial (Option (Option κ)) ('''+joint+''').E :=
  roughRemovedFactorPolynomial j frozen
    (alignmentJointExposedNativePolynomial D n v hv r b F q₀ w T x shift weight g a)

noncomputable def alignmentJointRemovedNativeSource
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    (Option (Option κ) → ℝ) → ('''+joint+''').G :=
  nativeVectorPolynomialSource ('''+joint+''')
    (alignmentJointRemovedNativePolynomial D n v hv r b F q₀ w T x j frozen shift weight g a)

theorem alignment_joint_removed_native_polynomial_degree
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    RoughVectorMvDegreeLE
      (alignmentJointRemovedNativePolynomial D n v hv r b F q₀ w T x j frozen shift weight g a)
      (((s*s+1)^(s+1))*max 1 T.card) :=
  rough_removed_factor_polynomial_degree j frozen
    (alignment_joint_exposed_native_polynomial_degree D n v hv r b F q₀ w T x shift weight g a)

theorem alignment_joint_removed_native_source_frozen_update
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ) (z : ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    alignmentJointRemovedNativeSource D n v hv r b F q₀ w T x j (Function.update frozen j z) shift weight g a =
      alignmentJointRemovedNativeSource D n v hv r b F q₀ w T x j frozen shift weight g a := by
  unfold alignmentJointRemovedNativeSource alignmentJointRemovedNativePolynomial
  rw [rough_removed_factor_polynomial_frozen_update]

theorem alignment_joint_removed_native_residual_packet
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G)
    (residue : Option κ → ℤ) (q : ℕ) :
    let p := alignmentJointRemovedNativePolynomial D n v hv r b F q₀ w T x j frozen shift weight g a
    let Q := alignmentJointRemovedNativeSource D n v hv r b F q₀ w T x j frozen shift weight g a
    RoughVectorMvDegreeLE (roughNativeResidualPolynomial p residue q)
      (((s*s+1)^(s+1))*max 1 T.card) ∧
    ∀ (z : ℝ) (y : Option κ → ℝ),
      roughVectorMvEval (roughNativeResidualPolynomial p residue q) (Option.elim · z y) =
        nativeLieGlobalLogarithm (E := ('''+joint+''').E)
          (I := ('''+joint+''').I) (G := ('''+joint+''').G)
          (roughNativeResidualSource ('''+joint+''') Q residue q (Option.elim · z y)) := by
  dsimp only
  constructor
  · exact rough_native_residual_polynomial_degree
      (alignment_joint_removed_native_polynomial_degree D n v hv r b F q₀ w T x j frozen shift weight g a) residue q
  · exact native_vector_polynomial_residual_log ('''+joint+''') _ residue q

'''
sample=source[source.index('theorem alignment_joint_exposed_native_source_actual_sample'):]
sample=sample[:sample.index(' := by')]
sample=sample.replace('alignment_joint_exposed_native_source_actual_sample','alignment_joint_removed_native_source_actual_sample')
sample=sample.replace('    (T : Finset (Fin N)) (hT :','    (j : Fin N) (T : Finset (Fin N)) (hT :')
sample=sample.replace('    let z := Sum.elim','    let z :=')
sample=sample.replace(')) (fun j : Fin N => (y j : ℝ))', '))')
sample=sample.replace('    alignmentJointExposedNativeSource D n v hv r b F q₀ w T x shift weight g a z =',
 '''    alignmentJointRemovedNativeSource D n v hv r b F q₀ w T x j (fun k => (y k : ℝ)) shift weight g a
      (Option.elim · (y j : ℝ) z) =''')
content+=sample+''' := by
  dsimp only
  apply native_vector_polynomial_source_sample
  rw [alignmentJointRemovedNativePolynomial,rough_removed_factor_polynomial_eval,Function.update_eq_self]
  have he := alignment_joint_exposed_native_source_actual_sample D n v hv r b
    hF hq hw T hT hx hy hkey p ell hp inc weight shift g a
  have hlog := alignment_joint_exposed_native_source_log D n v hv r b F q₀ w T x shift weight g a
    (Sum.elim (fun z : Option κ => match z with
      | none => (alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct y T) p
          ((alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)) ell : ℝ)
      | some z => (((alignmentNaturalBlockProduct y T : ℤ)*inc z : ℤ) : ℝ))
      (fun z : Fin N => (y z : ℝ)))
  exact hlog.trans (congrArg
    (nativeLieGlobalLogarithm (E := ('''+joint+''').E)
      (I := ('''+joint+''').I) (G := ('''+joint+''').G)) he)

end Hindman168
'''
Path('Hindman168/AlignmentJointRemovedNativeSource.lean').write_text(content,encoding='utf-8')
print('Created joint removed source, residual packet and actual simultaneous sample theorem.')
