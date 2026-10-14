from pathlib import Path

src = Path('Hindman168/NativeLatticeOrderedBasis.lean').read_text(encoding='utf-8')
src = src.replace('NativeCenterOrderedBasisExtension', 'NativeCenterOrderedSmoothBasisExtension')
src = src.replace('NativeLatticeOrderedBasisExist', 'NativeLatticeOrderedSmoothBasisExist')
src = src.replace('native_lattice_ordered_basis', 'native_lattice_ordered_smooth_basis')
src = src.replace('native_lattice_identity_model_ordered_basis', 'native_lattice_identity_model_ordered_smooth_basis')
src = src.replace('native_center_ordered_basis_extension', 'native_center_ordered_smooth_basis_extension')

old = '''    ∀ x, nativeOrderedExponentialCoordinates (I := I) (G := G) w x ∈ Γ ↔
      ∀ i, ∃ n : ℤ, x i = (n : ℝ)
'''
new = '''    (∀ x, nativeOrderedExponentialCoordinates (I := I) (G := G) w x ∈ Γ ↔
      ∀ i, ∃ n : ℤ, x i = (n : ℝ)) ∧
    NativeOrderedCoordinateSmoothInverse (I := I) (G := G) w
'''
assert src.count(old) == 1
src = src.replace(old, new)
old = '    Fintype.linearIndependent_iff.mpr (fun _ _ i => Fin.elim0 i), ?_, ?_⟩'
new = '    Fintype.linearIndependent_iff.mpr (fun _ _ i => Fin.elim0 i), ?_, ?_, ?_⟩'
assert src.count(old) == 1
src = src.replace(old, new)
old = '''      simpa only [nativeOrderedExponentialCoordinates, List.ofFn_zero, List.prod_nil] using Γ.one_mem

theorem'''
new = '''      simpa only [nativeOrderedExponentialCoordinates, List.ofFn_zero, List.prod_nil] using Γ.one_mem
  · refine ⟨fun _ => 0, ?_, ?_, contMDiff_const⟩
    · intro x
      funext i
      exact Fin.elim0 i
    · intro g
      exact Subsingleton.elim _ _

theorem'''
assert src.count(old) == 1
src = src.replace(old, new)
replacements = {
    'obtain ⟨m, hm, v, hv, hli, hbij, hlat⟩ := h':
        'obtain ⟨m, hm, v, hv, hli, hbij, hlat, hinv⟩ := h',
    'obtain ⟨w, hw, hwli, hwb, hwl⟩ := native_center_ordered_smooth_basis_extension':
        'obtain ⟨w, hw, hwli, hwb, hwl, hwi⟩ := native_center_ordered_smooth_basis_extension',
    '(fun i => (hv i).1) hli hbij hlat': '(fun i => (hv i).1) hli hbij hlat hinv',
    'w, hw, hwli, hwb, hwl⟩': 'w, hw, hwli, hwb, hwl, hwi⟩'
}
for old, new in replacements.items():
    assert src.count(old) == 1, old
    src = src.replace(old, new)
Path('Hindman168/NativeLatticeOrderedSmoothBasis.lean').write_text(src, encoding='utf-8')
print('Prepared strengthened actual smooth-inverse basis induction source.')
