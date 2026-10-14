from pathlib import Path
import ast
import re

prefix = 'round-native-relative-data'
old = 'round-relative-square-filtration'
modules = [
    'NativeRealIdealCosets', 'RelativeLieSubalgebra',
    'NativeRelativeSquareLieModel', 'NativeRelativeSquareExponentialSubgroup',
    'RelativeLinearModelSpan', 'NativeProductRationalInclusions',
    'NativeRelativeSquareRational', 'NativeRelativeSquareLatticeGeometry',
    'SubgroupStructureTransport', 'NativeRelativeSquareStructures',
    'NativeRelativeSquareMetric', 'NativeRelativeSquareData',
]
components = [
    'For ANY ACTUAL original REAL native Lie ideal, the ORIGINAL group coset criterion is NOW EXACTLY original global-logarithm difference membership. Genuine native BCH pair-ideal theorem applies via scalar restriction to arbitrary real vectors; actual ideal invariance and global inverses discharge all inputs. No rationality, quotient Exp/Log, lattice-normality or BCH identity premise.',
    'ACTUAL relative real model consists of two original vectors in original ideal A whose difference lies in original ideal B. Its genuine Lie-subalgebra bracket closure is PROVED from original ideal invariance and exact bilinear bracket difference. No supplied relative bracket closure.',
    'ACTUAL original stretched relative-square Lie subalgebra and ACTUAL product tangent model are NOW constructed from ORIGINAL native Lie lower-central ideals. Exact original model membership and genuine native product Lie-model equality are proved; actual original product Lie equivalence is used, not an assumed matrix model.',
    'ACTUAL exponential subgroup of constructed relative Lie algebra EQUALS SAME ORIGINAL relative-square subgroup literally. Genuine real-ideal coset/log criteria and retained exact group/Lie lower-central identification prove both inclusions. ACTUAL original relative square is NOW proved contractible and simply connected.',
    'ENTIRE ACTUAL relative linear model is EXACT sum of original layer diagonal image and original next-layer first-coordinate image, for nested original layers. Genuine inclusion and full-span equality are proved, without a spanning premise.',
    'ACTUAL original diagonal and first-coordinate embeddings preserve ACTUAL ORIGINAL product-lattice rational log span, using the true positive-power rational-hull criterion and original product exponential. No assertion that original nonabelian Log Gamma is an additive lattice.',
    'For EVERY positive fixed stretch and original layer index, GENUINE ACTUAL relative-model rationality against ORIGINAL product lattice is NOW PROVED. ORIGINAL rational lower-central layer spans plus genuine rational embeddings span the ENTIRE actual relative model. All layer/nesting/rational-inclusion inputs are discharged, with no rationality or adapted-basis assumption.',
    'ORIGINAL product-lattice intersection in SAME ORIGINAL relative-square group is NOW genuinely DISCRETE, CO-COMPACT and CLOSED. Actual coset quotient embeds CLOSEDLY into original product coset space, its original orbit is COMPACT and its actual quotient is metrizable. PROVED actual rationality/exponential-subgroup equality discharge ALL retained rational-subgroup lattice hypotheses.',
    'ACTUAL charted/Lie/boundaryless structures transport along PROVED literal subgroup equality while retaining ORIGINAL subgroup topology and ORIGINAL operations. Actual native source structures are supplied, rather than an assumed smooth compatibility.',
    'SAME ORIGINAL relative-square subgroup NOW has constructed native chart, Lie-infinity and boundaryless structures, through PROVED actual exponential-subgroup equality and genuinely proved original native Lie-subalgebra geometry. No Lie/boundaryless or merely compatible replacement-group assumption.',
    'An ACTUAL compatible metric on SAME ORIGINAL relative-square coset space is NOW constructed from PROVED original restricted-lattice discreteness/cocompactness and inherited original topology. Actual metric topology equality and original quotient map open/continuous are proved. No spatial Lipschitz inference from topology equality.',
    'GENUINE NativeNilmanifoldData(s) is NOW constructed on EXACT SAME ORIGINAL relative-square group, ACTUAL relative tangent subspace, ORIGINAL restricted product lattice and ACTUAL compatible metric. Literal original group/lattice identities and actual relative model TYPE equality are proved. ALL structural, connectedness, rational/lattice and metric inputs are discharged. SAME step bound s ONLY; actual reduced relative quotient, terminal model/rationality, Haar/sample/normalized-polynomial compatibility and NONZERO quantitative inverse still remain open.',
]
source = Path(old+'-audit.py').read_text(encoding='utf-8')
remaining = ast.literal_eval(re.search(r'^REMAINING = (.*)$',source,re.M).group(1))
start = 'Actual relative rational Lie model, original restricted-lattice cocompactness, native quotient structures/metric/canonical Haar, normalized shifted polynomial membership and finite original shifted observable transport still remain open.'
replacement = ('ACTUAL original relative-square REAL Lie model and genuine original exponential-subgroup equality are NOW PROVED, with actual contractible/simply-connected original relative group. ENTIRE actual relative model is NOW PROVED RATIONAL against ORIGINAL product-lattice log span, from original rational lower-central layers and actual diagonal/coordinate embeddings. ORIGINAL restricted product lattice is NOW PROVED discrete/cocompact/closed, with true closed coset embedding and compact original relative orbit. Actual original relative subgroup chart/Lie-infinity/boundaryless and compatible metric/topology/open quotient are constructed. GENUINE NativeData(s) NOW uses EXACT SAME ORIGINAL relative-square group/model/restricted lattice/metric; literal group/lattice and proved actual model equality are retained. SAME step bound s only. Actual reduced relative quotient by terminal diagonal still needs native model/image-lattice geometry and canonical Haar/sample/normalized shifted polynomial compatibility; terminal-layer Fourier and NONZERO quantitative Leibman remain open.')
assert start in remaining
remaining = remaining.replace(start,replacement)
remaining = remaining.replace('NEXT construct actual rational relative-square Lie model and original restricted lattice geometry, then terminal-layer Fourier and normalized polynomial/observable identities needed for genuine NONZERO quantitative Leibman induction.',
    'NEXT actual original relative native inclusion smoothness/identity derivative/Exp-Log compatibility, actual terminal diagonal subspace and rational central quotient native geometry, then terminal-layer Fourier and normalized polynomial/observable/Haar identities needed for genuine NONZERO quantitative Leibman degree induction.')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',['Hindman168/'+m+'.lean' for m in modules]),('COMPONENTS',components),('REMAINING',remaining)]:
    source = re.sub(r'^'+name+r' = .*$',lambda _:name+' = '+repr(value),source,flags=re.M)
source = source.replace('Audit actual relative-square group filtration, terminal diagonal and genuine original algebraic filtration-degree reduction.', 'Audit genuine original rational relative-square Lie geometry, restricted lattice and exact original native relative data.')
source = source.replace('06_rough_progressions and Green-Tao section 7: ACTUAL relative-square original subgroup filtration and genuine quotient FILTRATION-degree reduction; relative rational native geometry/polynomial normalization/nonzero quantitative Leibman/full prize theorem open', '06_rough_progressions and Green-Tao section 7: GENUINE ORIGINAL rational relative Lie model, actual restricted lattice and EXACT ORIGINAL relative NativeData(s); reduced terminal quotient geometry/Haar/normalized polynomial/nonzero quantitative Leibman/full prize theorem open')
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
print('Prepared '+prefix+'-audit.py for '+str(len(modules))+' modules')
