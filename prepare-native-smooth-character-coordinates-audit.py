from pathlib import Path
import json
import re

prefix = 'round-native-smooth-character-coordinates'
old = 'round-native-lattice-smooth-coordinates'
modules = ['Hindman168/'+m+'.lean' for m in [
    'NativeOrderedCharacterEvaluation', 'NativeSmoothBasisCharacterIntegrality',
    'NativeSmoothBasisIntegerCharacters', 'NativeSmoothBasisIntegerCharacterGrid',
    'NativeSmoothIntegerCharacterNormalization']]
components = [
    'Every actual horizontal logarithmic character evaluates the original ordered exponential product as the exact linear sum of its actual basis evaluations. The character is smooth on the original group. The same evaluation law holds in the actual inverse coordinates of the fixed original lattice Diffeomorph.',
    'For the same fixed smooth ordered lattice real basis, a functional killing the actual original commutator layer is integral on the entire original Gamma if and only if its actual evaluations on every fixed basis column are integers. The reverse direction uses actual original Gamma/integer ordered-coordinate membership and character additivity, not an additive Log Gamma lattice.',
    'Integer coefficient vectors on the fixed smooth original lattice basis injectively parameterize real linear functionals. Their actual horizontality is equivalent to finitely many linear equations using the actual rational original bracket structure constants. Nonzero horizontal integer vectors are exactly nonzero Gamma-integral horizontal functionals; every such functional has a unique integer vector.',
    'A finite horizontal character grid is constructed directly from bounded integer evaluations on that same smooth original lattice basis. Its membership is characterized exactly, its cardinality is at most (2*B+1)^dim(E), and every actual horizontal functional with bounded basis evaluations belongs. A bound on the full Euclidean integer vector places the character in the grid with ceiling budget fixed before source data.',
    'For every character in that actual finite integer grid, a normalized rational direction and a positive original lattice period at most B are constructed explicitly from a nonzero integer coefficient. Direction and bounded period functions are chosen simultaneously over the entire fixed finite grid before varying source data.'
]
remaining = json.loads(Path('verification-manifest.json').read_text())['last_round']['remaining']
gap = "The full evaluation-vector norm is not yet identified with the paper's filtration-adapted horizontal coordinate norm, and no analytic character existence input is discharged."
assert remaining.count(gap) == 1
remaining = remaining.replace(gap,
    'For the same smooth original lattice-coordinate basis, exact character linear evaluation, the two-way Gamma-integrality/integer-evaluation criterion, unique integer differential representation, finite rational bracket equations and a direct bounded-integer horizontal grid are now proved. Every character in this direct grid has a normalized rational direction with an explicitly positive original lattice period at most the fixed integer grid budget. The Euclidean size here is the full integer vector in that smooth basis; it is still not identified with the paper filtration-adapted horizontal coefficient norm. No analytic character existence or modular binomial coefficient bound is discharged.')
review = [
    'The original noncommutative ordered List product is retained. Additivity is proved from the actual original logarithmic product error lying in the commutator layer; only after applying that genuine character is the ordered product converted to a scalar sum. The zero identity uses the actual original global logarithm at one.',
    'Smoothness is proved by composing the actual continuous linear functional with the genuine original smooth global logarithm. It requires no character nonzero or lattice assumption. All inverse-coordinate evaluations use the SAME strengthened smooth basis choice as the actual original Diffeomorph.',
    'The reverse lattice-integrality implication takes a genuine original Gamma element, applies the actual original smooth inverse coordinates, uses the proved exact original lattice/integer-coordinate predicate, and constructs its integer character value as the finite integer dot product. The other direction tests actual original exponentials of the fixed basis columns.',
    'The finite horizontality test uses real-basis extensionality in both slots of the actual continuous bilinear adjoint differential. Its reverse implication proves annihilation of ALL actual brackets before invoking the proved commutator span theorem. Its forward implication uses actual next-layer membership of adjoint generators. It does not replace full horizontality by unproved basis tests.',
    'The integer functional uses actual real basis construction. Its injectivity uses evaluation on the full fixed spanning basis and injectivity of integer cast; zero, nonzero and unique-representation laws include the zero-dimensional case. Integrality of every admissible integer functional is discharged by the two-way original Gamma criterion.',
    'The finite equations use real coordinates of the original adjoint differential in the same smooth real basis. Their rationality is already proved by the registered same-basis rational-coordinate theorem. These equations are not claims of an additive lattice of original group logarithms or arbitrary integer logarithm coordinates.',
    'The fixed finite grid enumerates all integer vectors in the actual closed integer box, maps them to actual functionals, and filters to genuine nonzero Gamma-integral horizontal functionals. Its exact membership, cardinal bound and completeness under a supplied coefficient bound are separately proved. The full Euclidean vector bound is supplied; no bound from non-equidistribution is asserted.',
    'Normalization selects a nonzero actual integer coefficient n, takes the rational direction n^-1 times its genuine original lattice basis column, and period natAbs(n). Its original exponential is the genuine column exponential or its inverse according to the sign of n. Hence the period is positive and at most the fixed integer box budget. This discharges original lattice membership directly without assuming an additive lattice of logarithms; simultaneous grid choices retain the uniform period bound and include empty-grid cases.',
    'Full prescribed filtration adaptation, the paper horizontal coordinate norm conversion, quantitative Leibman existence and modular coefficient bounds, final StrongConjecture, unavoidable obstruction, independent replay and prize eligibility remain unclaimed.',
    'All retained registered proof sources and axiom sets are checked unchanged. Focused autoImplicit=false compilation, full build, standard-only selected axiom reports, source scans and all six pinned primary sections are author-side verification, not independent kernel replay.'
]
src = Path(old+'-audit.py').read_text(encoding='utf-8')
src = re.sub(r'^PREFIX = .*$', 'PREFIX = '+repr(prefix), src, count=1, flags=re.M)
src = re.sub(r'^OLD = .*$', 'OLD = '+repr(old), src, count=1, flags=re.M)
a = src.index('MODULES = '); b = src.index('\ndef declarations():', a)
src = src[:a]+f'MODULES = {modules!r}\nCOMPONENTS = {components!r}\nREMAINING = {remaining!r}\n'+src[b:]
a = src.index('        application_review=COMPONENTS+'); b = src.index('\n        verified=summary', a)
src = src[:a]+f'        application_review=COMPONENTS+{review!r}+[REMAINING],'+src[b:]
src = re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions exact original horizontal integer coordinates in the same smooth ordered lattice basis; full filtration adaptation and quantitative existence remain open'", src)
Path(prefix+'-audit.py').write_text(src, encoding='utf-8')
print('Prepared exact original smooth-basis character audit for', len(modules), 'modules.')
