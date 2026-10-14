from pathlib import Path

source=Path('Hindman168/AlignmentNativeCompleteCubeCountableSelection.lean').read_text(encoding='utf-8')
start=source.index('variable {ι : Type}')
end=source.index('\ninclude n v hv r b in',start)
source=source[:start]+'''variable {ι : ℕ → Type} [∀ q, Fintype (ι q)]
  {κ : ℕ → Type} [∀ q, Fintype (κ q)]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ∀ q, ι q → NativeNilmanifoldData.{u} s) (n : ∀ q, ι q → ℕ)
  (v : ∀ q ν, Fin (n q ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ q ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D q ν).E) (I := (D q ν).I) (G := (D q ν).G) (n q ν) (v q ν)))
  (r : ∀ q, ι q → ℕ) (b : ∀ q ν, Basis (Fin (r q ν)) ℝ
    (alignmentNativeArrayData (D q ν) (n q ν) (v q ν) (hv q ν)).E)
''' +source[end:]
source=source.replace('alignment_native_complete_cube_countable_supported_selection','alignment_all_targets_native_cube_countable_supported_selection')
source=source.replace('(T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)','(T : ℕ → Finset (Fin N)) (hT : ∀ q j, j ∈ T q → j < i)')
source=source.replace('→\n      ι → AlignmentAddingPair N i → ℤ','→\n      ι _q → AlignmentAddingPair N i → ℤ')
# Make the source index explicit in dependent source families.
source=source.replace('(shift : ℕ → ℕ →','(shift : ∀ _q _w : ℕ,')
source=source.replace('∀ ν, (D ν).G','∀ ν, (D _q ν).G')
source=source.replace('D n v hv F q₀ (W j) T','(D q) (n q) (v q) (hv q) F q₀ (W j) (T q)')
source=source.replace('F (W j) i T','F (W j) i (T q)')
source=source.replace('(κ := κ q) D n v hv r b','(κ := κ q) (D q) (n q) (v q) (hv q) (r q) (b q)')
source=source.replace('hF q₀ hq T hT','hF q₀ hq (T q) (hT q)')
source=source.replace('positive events, simultaneously for a countable list of ACTUAL native complete cube',
    'positive events, simultaneously for countably many HETEROGENEOUS original target/model families and actual native complete cube')
source=source.replace('Every condition retains uniformity over all its endpoints/tests.',
    'The target, model index type, native groups, determining evaluations, basis, cube dimension and numerical data may vary with each fixed condition. Every condition retains all endpoint/test quantifiers.')
Path('Hindman168/AlignmentAllTargetsNativeCountableSelection.lean').write_text(source,encoding='utf-8')
print('Prepared heterogeneous original all-target native selection')
