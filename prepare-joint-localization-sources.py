from pathlib import Path

# Specialize the already reviewed argument to actual inputs in both factors.
# The retained sources are only read; all changes are written to new modules.
products = Path('Hindman168/LocalizedMixedDualProducts.lean').read_text(encoding='utf-8')
products = products.replace('import Hindman168.LocalizedMixedDualSpan', 'import Hindman168.JointMixedDualSpan')
products = products.replace('localizedMixedDual', 'jointMixedDual')
products = products.replace('Exact products of localized actual duals', 'Exact products of actual duals with inputs in both factors')
products = products.replace('Among actual unit members of the second space', 'Among actual unit members of the original intersection')
products = products.replace('(hs : ∀ w, ∑ c, p w c = 1) (he : 0 < e)',
    '(hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d) (he : 0 < e)')
old_hf = '(hf : ∀ i ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f i ω) ∈ mixedDualHilbertSubspace p R e U)'
assert products.count(old_hf) == 1
products = products.replace(old_hf,
    '(hf : ∀ i ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f i ω) ∈\n'
    '      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U)')
start = products.index('    have ht : ∀ ω,')
end = products.index('    let C :=', start)
products = products[:start] + '''    have ht : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (t ω) ∈
        mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U := by
      intro ω hω
      apply mixedDualHilbert_intersection_shifted_product p Q d U R e hs hd he
        (fun i => f i ω) (fun i => hu i ω) (fun i => hf i ω hω)
        (fun i w _ => ∑ j ∈ ω, (a w i j : G w)) (t ω)
      intro w c x
      rfl
''' + products[end:]
old_hr = '(hR : hilbertFamilyToCompletion _ U g ∈ mixedDualHilbertSubspace p R e U)'
assert products.count(old_hr) == 2
products = products.replace(old_hr,
    '(hboth : hilbertFamilyToCompletion _ U g ∈\n'
    '      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U)')
products = products.replace('=> hR)', '=> hboth)').replace('g hg hR ho', 'g hg hboth ho')
products = products.replace('p Q d U R e hs he', 'p Q d U R e hs hd he')
Path('Hindman168/JointMixedDualProducts.lean').write_text(products, encoding='utf-8')

density = Path('Hindman168/LocalizedMixedDualDensity.lean').read_text(encoding='utf-8')
density = density.replace('LocalizedMixedDualProducts', 'JointMixedDualProducts')
density = density.replace('localizedMixedDual', 'jointMixedDual')
density = density.replace('genuine localized dual generators', 'genuine dual generators whose inputs retain both factors')
density = density.replace('The actual localized generator span', 'The actual generator span with inputs in both factors')
density = density.replace('(hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (he : 0 < e)',
    '(hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d) (he : 0 < e)')
density = density.replace('jointMixedDualHilbert_unit_product_closed p Q d U R e hs he',
    'jointMixedDualHilbert_unit_product_closed p Q d U R e hs hd he')
density = density.replace('jointMixedDualHilbert_projection_exact_representative p Q d U R e hU hs he',
    'jointMixedDualHilbert_projection_exact_representative p Q d U R e hU hs hd he')
density = density.replace('(f - t) hrunit hrR hro', '(f - t) hrunit ⟨hrQ, hrR⟩ hro')
Path('Hindman168/JointMixedDualDensity.lean').write_text(density, encoding='utf-8')
print('Prepared new products and density modules with joint input membership, leaving retained sources unchanged.')
