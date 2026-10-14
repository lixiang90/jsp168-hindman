from pathlib import Path
import re

source = Path('round-piece-refinement-hilbert-audit.py').read_text(encoding='utf-8')
source = source.replace('actual piece refinement and Hilbert clipping increment', 'actual product quotient and representation increment')
source = source.replace("PREFIX = 'round-piece-refinement-hilbert'", "PREFIX = 'round-product-nil-representation'")
source = source.replace("OLD = 'round-ultrafilter-inner-core'", "OLD = 'round-piece-refinement-hilbert'")
counts = {'939': '945', '945': '951', '927': '933', '936': '942', '4545': '4570', '28': '25', '20': '18'}
source = re.sub(r'\b(?:939|945|927|936|4545|28|20)\b', lambda m: counts[m[0]], source)
source = source.replace('new_instances=1', 'new_instances=0')
modules = ['ProductCosetQuotient', 'ProductCosetMetric', 'ProductPieceNilRepresentation',
           'BoundedRealProductLipschitz', 'ProductPieceNilMultiplication', 'ProductLatticeGeometry']
components = [
    'The NATURAL coset map from (G x H)/(Gamma x Lambda) to G/Gamma x H/Lambda is bijective and is a homeomorphism for the original group topologies. Neither lattice is assumed normal.',
    'The product quotient metric is induced through that exact natural coset equivalence, which is an isometry for the product metric. Compactness is transferred. When the factor metric quotient maps are open quotient maps, the product map is an open quotient map and its metric topology is proved EQUAL to the original quotient topology.',
    'Actual original piecewise orbit sums use the product group and SAME product lattice with observable f(z1)+g(z2); the original globally anchored integer powers and stage/piece indices are preserved exactly. Global observable bounds and Lipschitz constants are B1+B2 and L1+L2. Scalar multiplication is realized on the same quotient.',
    'Actual pointwise products use observable f(z1)*g(z2) on the same product quotient. A fully proved bounded-product Lipschitz estimate gives bound B1*B2 and Lipschitz constant B1*L2+B2*L1, uniformly in all stages and pieces.',
    'The actual product lattice is discrete if its factors are discrete, and its original coset space is compact if the factors are compact. A common nilpotence-class bound s is preserved by the product, using the exact max formula for the product class.'
]
remaining = (
    'Original native geometry, original-law Hilbert construction, actual piece refinement, closed-span '
    'nesting and clipping contraction remain proved. Binary product-quotient representation is NOW PROVED '
    'for addition and multiplication, with exact original powers, product lattices, explicit uniform '
    'observable/Lipschitz bounds and preservation of compactness, lattice discreteness and nilpotence-step '
    'bounds. The induced product metric is proved compatible with the original quotient topology under '
    'the explicit factor metric quotient-map compatibility conditions. Scalar multiplication on the same '
    'quotient is also proved. Next assemble the finite recipe/product closure with complete native '
    'manifold data and uniform common complexity, construct the full admissible step-at-most-s '
    'nilsequence closed span, and instantiate clipped dense approximation and Ramsey selection with '
    'the paper\'s padding/principal tuple indexing. Calibration/Alignment, subgroup inverse inputs, '
    'actual coloring/arithmetic data, ordered positive rapidly separated monochromatic witnesses and '
    'quantitative bounds where required remain. Original models, groups, Gamma, laws and StrongConjecture '
    'are unchanged. The full target remains unproved. No unavoidable blocker is established; '
    'publication, PR and prize application remain pending.'
)
start = source.index('MODULES = ')
end = source.index('\n\ndef declarations', start)
source = source[:start] + 'MODULES = ' + repr(['Hindman168/'+m+'.lean' for m in modules]) + '\n' + \
    'COMPONENTS = ' + repr(components) + '\nREMAINING = ' + repr(remaining) + '\n' + source[end:]
review = [
    'PROGRESS. Previous audit rechecked before edits. All 945 retained baseline hashes are checked at registration. Only root imports and registry change; prior proof sources, original statements, original models/lattices/laws, pins and attribution remain intact.',
    'The source route is 05_prediction.tex: products and Lipschitz real combinations of finitely many representing families are represented using product nilmanifolds. This increment proves the exact binary algebraic/metric construction and basic lattice/step preservation; it does not claim the entire finite native recipe package.',
    'ProductCosetMap is constructed on genuine left-coset quotients by Quotient.lift. Well-definedness and injectivity use the exact relation a^{-1}b in Gamma x Lambda coordinatewise; surjectivity uses representatives of each factor. No normality hypothesis or quotient-group multiplication is used.',
    'The topological equivalence uses actual open quotient maps of topological groups. The inverse continuity is checked after composition with the product of the original quotient maps, rather than inferred from an arbitrary set bijection.',
    'ProductCosetMetric uses the natural bijection to transport the product metric. The factor metric topologies and the product metric topology are explicit in the compatibility theorem, preventing accidental synthesis of an unrelated quotient topology. The actual induced metric topology is proved equal to the original coinduced quotient topology when the factor metrics have their original quotient maps.',
    'The sum observable is constructed as an actual continuous map on the product quotient. Projection maps are 1-Lipschitz, so the Lipschitz constants add. Exact product-group integer powers prove the original piecewise sequence identity; translations and basepoints are paired without changing intervals, modulus or original laws.',
    'The multiplication estimate expands f(x)g(x)-f(y)g(y), uses global observable bounds and factor Lipschitz estimates, and obtains Bf*Lg+Bg*Lf. This avoids an invalid claim that multiplication is globally Lipschitz on all of R x R. The resulting bound is independent of w and the number of pieces.',
    'The same specified Gamma and Lambda are used throughout. Product lattice discreteness is transported by the natural subtype-product homeomorphism. Original quotient compactness uses the natural coset homeomorphism. The common step bound follows from the exact max of the two nilpotence classes.',
    'Arbitrary finite sums/products, full native product manifold packaging, admissible recipe selection and uniform common complexity still need assembly. No broad closed-span density, full Calibration/Alignment, StrongConjecture, publication or prize-submission claim is made. No unavoidable blocker is established.'
]
start = source.index('        application_review=[')
end = source.index('], new_modules=MODULES', start) + 1
source = source[:start] + '        application_review=' + repr(review) + source[end:]
Path('round-product-nil-representation-audit.py').write_text(source, encoding='utf-8')
print('Prepared six-module audit: 18 theorems, 7 definitions, 25 reports.')
