from pathlib import Path
import re

source = Path('round-ultrafilter-inner-core-audit.py').read_text(encoding='utf-8')
source = source.replace('original-law ultrafilter Hilbert construction', 'actual piece refinement and Hilbert clipping increment')
source = source.replace("PREFIX = 'round-ultrafilter-inner-core'", "PREFIX = 'round-piece-refinement-hilbert'")
source = source.replace("OLD = 'round-projection-gap-energy'", "OLD = 'round-ultrafilter-inner-core'")
counts = {'933': '939', '939': '945', '921': '927', '930': '936', '4517': '4545', '42': '28', '21': '20'}
source = re.sub(r'\b(?:933|939|921|930|4517|42|21)\b', lambda m: counts[m[0]], source)
source = source.replace('new_definitions=10, new_instances=11', 'new_definitions=7, new_instances=1')
source = source.replace('== old.AXIOM_FREE', "== old.AXIOM_FREE | {'Hindman168.intervalResidueParent'}")
modules = ['NilPieceRefinement', 'BoundedPieceNilFamilies', 'PieceNilHilbertSubspace',
           'PieceNilLipschitzComposition', 'FiniteMassHilbertClipping', 'PieceNilHilbertClipping']
components = [
    'The exact original piecewiseLinearNilsequence is preserved by interval refinement whenever the fine length divides the coarse length. An explicit parent interval/residue map works for ALL integer inputs, keeps the modulus and the global y/M orbit exponent unchanged, and master-parameter ordered gaps supply the divisibility.',
    'Actual bounded piecewise orbit representations on a fixed quotient have a single observable bound and Lipschitz constant across all stages and pieces. Refinement preserves these exact constants and the same quotient, translations and basepoints by reindexing.',
    'These actual representing families are realized in the ORIGINAL-law ultrafilter Hilbert space. Their actual closed linear spans are proved nested under refinement, have genuine orthogonal projections, and satisfy the exact paper projection-energy identity.',
    'Arbitrary Lipschitz real composition of the actual observables preserves representation on the SAME quotient with explicit global bound K*B+abs(psi(0)) and Lipschitz constant K*Lip. In particular unit-interval clipping preserves the representing family.',
    'Unit-interval clipping contracts distance to [0,1]-valued targets pointwise, in the ORIGINAL weighted L2 seminorm, and in the actual completed ultrafilter Hilbert space. Clipped genuine representatives remain in the actual closed span; Pythagorean decomposition then proves the actual projected-distance contraction.'
]
remaining = (
    'Original native geometry and original-law ambient ultrafilter Hilbert space remain proved. The exact '
    'piecewise orbit definition now has proved interval refinement, uniform-bound/Lipschitz preservation, '
    'actual Hilbert realization and closed-span nesting with genuine projection energy identity on each '
    'fixed quotient. Lipschitz real composition and unit-interval clipping of genuine representatives '
    'are proved, including original weighted L2 and projected-distance contraction. These general '
    'fixed-quotient lemmas do NOT yet construct the entire space of all step-at-most-s nilmanifold recipes. '
    'Next prove product-quotient representation and finite linear-combination/common-complexity closure, '
    'assemble the full admissible nilsequence closed spans, then instantiate clipped dense approximation '
    'and Ramsey selection with the paper\'s padding/principal tuple indexing. Calibration/Alignment, '
    'subgroup inverse inputs, actual coloring/arithmetic data and ordered positive rapidly separated '
    'monochromatic witnesses, plus quantitative bounds where required, remain. The original models, '
    'groups, Gamma, sampling laws and StrongConjecture statement are unchanged. StrongConjecture and '
    'the prize target are unproved. No unavoidable blocker is established; publication, PR and prize '
    'application remain pending.'
)
start = source.index('MODULES = ')
end = source.index('\n\ndef declarations', start)
source = source[:start] + 'MODULES = ' + repr(['Hindman168/'+m+'.lean' for m in modules]) + '\n' + \
    'COMPONENTS = ' + repr(components) + '\nREMAINING = ' + repr(remaining) + '\n' + source[end:]
review = [
    'PROGRESS. Prior audit rechecked before edits. All 939 baseline source/config hashes checked before registration; only root imports and registry change. Original statements, retained proofs, source pins, groups, lattices and sampling laws remain unchanged.',
    'The source route is 05_prediction.tex nested-spaces and the clipping argument in energy-selection. The implementation uses the RETAINED actual piecewiseLinearNilsequence, not a newly substituted simplified orbit definition.',
    'The explicit parent map is (intervalIndex / (coarseLength/fineLength), residue). The proof uses exact natural divisibility and integer Euclidean division with nonnegative divisor, so it covers negative roots as well. The original orbit is globally anchored at y/M, so reindexing suffices without a fictitious basepoint shift. Ordered master gaps provide actual divisibility.',
    'IsBoundedPieceNilsequence retains one B and one Lip valid at every w, every piece and every quotient point. Translations and basepoints may vary freely, as in the retained tests. Refinement copies these constants exactly. The fixed quotient is arbitrary in this general lemma; no nilpotence, compactness or step bound is falsely inferred from the name.',
    'Hilbert generators are actual canonical images of L2-bounded original-law families satisfying this representation predicate. Probability laws and the global observable bound prove every representing family has such an image. Closed spans use actual Submodule.span and topologicalClosure. Generator inclusion proves closed-span inclusion; completeness supplies the genuine orthogonal projections.',
    'Real Lipschitz composition is built by actual continuous-observable composition with the same g, x and quotient. The global bound is K*B+abs(psi(0)), and the new Lipschitz constant is K*Lip. UnitIntervalClip is explicitly max 0 (min 1 t), is 1-Lipschitz, and fixes every [0,1] target.',
    'Clipping contraction is proved in the original coordinate L2 seminorm using nonnegative original weights and the actual support; zero weights are untouched. The ultrafilter comparison of squared-distance limits passes this inequality to the SAME completed Hilbert space. The target need only be [0,1]-valued on the original supports.',
    'Clipped genuine representatives are proved to belong to the actual generator set and hence the actual closed span. The retained Pythagorean comparison proves contraction relative to the genuine orthogonal projection. This does not claim that finite linear combinations of arbitrary recipes are already represented: product-quotient closure and finite common complexity are still required.',
    'All retained empty-axiom reports are preserved. The new pure integer parent-map definition is expected to have an empty axiom report; its exact name is checked. Every other report remains restricted to the standard foundational axioms. No full-target or publication claim is made; no unavoidable blocker is established.'
]
start = source.index('        application_review=[')
end = source.index('], new_modules=MODULES', start) + 1
source = source[:start] + '        application_review=' + repr(review) + source[end:]
Path('round-piece-refinement-hilbert-audit.py').write_text(source, encoding='utf-8')
print('Prepared six-module audit: 20 theorems, 7 definitions, 1 instance, 28 reports.')
