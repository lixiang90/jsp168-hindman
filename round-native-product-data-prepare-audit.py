from pathlib import Path
import re

source = Path('round-product-nil-representation-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-product-nil-representation'", "PREFIX = 'round-native-product-data'")
source = source.replace("OLD = 'round-piece-refinement-hilbert'", "OLD = 'round-product-nil-representation'")
counts = {'945':'951','951':'958','933':'940','942':'949','4570':'4620','25':'50','18':'15'}
source = re.sub(r'\b(?:945|951|933|942|4570|25|18)\b', lambda m: counts[m[0]], source)
source = source.replace('new_module_count=6', 'new_module_count=7')
source = source.replace('new_instances=0', 'new_instances=0, new_structures=1, new_structure_instance_projections=18, new_generated_reports=27')
modules = ['NativeLieGlobalTopology', 'NativeNilmanifoldData', 'NativeNilmanifoldConstruction',
           'NativePieceRecipes', 'NativeFiniteRecipeClosure', 'NativeNilmanifoldTrivial', 'NativeFiniteRecipeBounds']
components = [
    'The actual native exponential and global logarithm form a homeomorphism between the original real model and group. Native groups are contractible, permitting the genuine product simply-connected manifold instance.',
    'NativeNilmanifoldData retains the original finite-dimensional real model, Lie manifold, connected simply connected nilpotent group, specified discrete cocompact lattice, step bound and compatible quotient metric. Every original native input supplies these data using the actual exponential homeomorphism and natural compact quotient metric.',
    'The product of two complete native data packages is constructed on the original product group and product lattice, with the product manifold charts, same step bound and exact compatible product quotient metric. No product geometry is postulated.',
    'Native piecewise representations are closed under addition, multiplication, scalar multiplication, clipping and piece refinement. Finite real linear combinations are represented on actual native product nilmanifolds, and finitely many functions share one native nilmanifold.',
    'A genuine zero-dimensional trivial native Lie nilmanifold supplies the empty-family case. Every finite family of native representations has one common native space and one common observable bound and Lipschitz constant, uniformly over all labels, stages, pieces and quotient points.'
]
remaining = ('Native geometry, original-law Hilbert construction, piece refinement, fixed-quotient closed-span nesting and clipping contraction remain proved. Full native product data, finite linear combination closure and simultaneous finite representations with common global observable and Lipschitz bounds are now proved, including empty families. These are existential bounds for each finite family, not a quantitative bound in external complexity parameters. Next construct the full admissible step-at-most-s represented Hilbert subspace and its closure, instantiate clipped dense approximation and Ramsey selection with the paper padding/principal tuple indexing. Calibration/Alignment, subgroup inverse inputs, actual coloring/arithmetic data, ordered positive rapidly separated monochromatic witnesses and quantitative bounds where required remain. Original models, groups, Gamma, laws and StrongConjecture are unchanged. The full target remains unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start = source.index('MODULES = ')
end = source.index('\n\ndef declarations', start)
source = source[:start] + 'MODULES = ' + repr(['Hindman168/'+m+'.lean' for m in modules]) + '\nCOMPONENTS = ' + repr(components) + '\nREMAINING = ' + repr(remaining) + '\n' + source[end:]
fields = 'E normedAdd normedReal completeModel rationalModule finiteModel H modelTopology I G groupTopology charted group topologicalGroup lie boundaryless hausdorff nilpotent connected simplyConnected step_le Γ latticeDiscrete quotientCompact metric metric_quotientMap'.split()
assert len(fields) == 26
source = source.replace('    return {p: old.declarations(p) for p in MODULES}', '''    ds = {p: old.declarations(p) for p in MODULES}
    data = ds['Hindman168/NativeNilmanifoldData.lean']
    data.append(('structure', 'NativeNilmanifoldData'))
    data.append(('constructor', 'NativeNilmanifoldData.mk'))
    data.extend(('projection', 'NativeNilmanifoldData.' + f) for f in ''' + repr(fields) + ''')
    return ds''')
review = [
    'PROGRESS. Previous audit rechecked before edits. All 951 baseline hashes checked before registration. Only root imports and axiom registry change among retained files; original targets and previous proofs remain intact.',
    'Follows the product nilmanifold route in fixed 05_prediction.tex. Complete native data witnesses are retained rather than replacing the original group with a matrix model. The construction from native hypotheses proves the package is available on the same model, group and lattice.',
    'Simply connected product geometry is obtained from native exponential/logarithm homeomorphisms and contractibility of real vector models. The manifold chart target is ModelProd, and all product Lie, boundaryless, finite-dimensional, complete and topological instances are checked by Lean.',
    'Metric quotient topology is explicit in all compatibility statements and continuous observable types, avoiding competing automatic quotient and metric topology instances. Product space uses exactly the previously verified natural coset product metric.',
    'The structure introduces no axiom. Its constructor and all 26 projections, including 18 registered instance projections, are included individually in the kernel axiom registry, in addition to every explicit definition and theorem.',
    'Finite common representation uses induction, actual product embedding of each factor by addition of zero, and preservation of each represented function. Finite real sums are submodule closure. Constant, scalar, product and clipped recipes use the existing exact original piecewise orbit laws.',
    'The empty-family seed is an actual PUnit zero-dimensional Lie group with top lattice and nilpotence class zero. No nonempty index or positive step hypothesis is silently introduced.',
    'Uniform bounds have quantifier order: for each finite represented family, there exist one D, one B and one Lip, followed by all labels, stages, pieces and points. B and Lip are finite sums of individual nonnegative bounds. This does not supply quantitative complexity estimates uniform over all possible input families.',
    'Full admissible Hilbert closure, paper indexing, Calibration/Alignment and the final combinatorial target remain. No completed StrongConjecture or unavoidable blocker is claimed.'
]
start = source.index('        application_review=[')
end = source.index('], new_modules=MODULES', start) + 1
source = source[:start] + '        application_review=' + repr(review) + source[end:]
Path('round-native-product-data-audit.py').write_text(source, encoding='utf-8')
print('Prepared native data audit: 7 definitions, 15 theorems, 1 structure, 27 generated reports.')
