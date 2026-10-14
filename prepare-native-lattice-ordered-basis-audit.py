from pathlib import Path
import json, re

prefix = 'round-native-lattice-ordered-basis'
old = 'round-native-lattice-ordered-coordinates'
modules = ['Hindman168/'+m+'.lean' for m in [
    'ProjectionAppendIndependent', 'NativeCenterLatticeIndependent',
    'NativeCenterOrderedBasisExtension', 'NativeLatticeOrderedBasis',
    'NativeLatticeOrderedRealBasis', 'NativeLatticeOrderedRationalBasis',
    'NativeLatticeOrderedBasisCoordinates', 'NativeLatticeOrderedIntegerEvaluations']]
components = [
    'Projected independent quotient lifts appended to independent kernel columns are linearly independent. Actual original central lattice columns satisfy these hypotheses, and native center dimension induction now constructs original ordered lattice coordinates whose vector columns form an actual real basis.',
    'A fixed real basis of the original model is chosen with all exponentials in the actual original Gamma, every column in the actual rational logarithmic span, a bijective actual ordered exponential product map, and exact original Gamma membership if and only if all parameters are integers. The same original columns form an actual rational basis of the original rational logarithmic span.',
    'The actual ordered lattice rational and real bases have identical original columns. Their actual coordinate square commutes; membership in the original rational logarithmic span is equivalent to rationality of every real coordinate. The actual original adjoint differential structure constants in this ordered basis are rational.',
    'Every original Gamma-integral logarithmic linear functional has unique integer evaluations on the fixed original ordered lattice basis. These evaluations vanish exactly for the zero functional. A Euclidean bound on the full integer evaluation vector places an actual horizontal functional in the fixed original norm-budget character grid without a further evaluation-identification premise.'
]
remaining = json.loads(Path('verification-manifest.json').read_text())['last_round']['remaining']
old_gap = 'Linear basis independence of the chosen vector family, smooth inverse and adaptation of the ordered basis to all specified filtration layers have not yet been proved; the coordinate existence theorem alone does not discharge those requirements.'
new_gap = 'The chosen original ordered vector family is now proved linearly independent and upgraded to an actual real basis and an identical-column rational basis of the original logarithmic span, with rational original bracket structure constants and actual unique integral functional evaluations. Smooth inverse and adaptation of the ordered lattice basis to all specified filtration layers remain unproved. The full evaluation-vector norm is not yet identified with the paper\'s filtration-adapted horizontal coordinate norm, and no analytic character existence input is discharged.'
assert remaining.count(old_gap) == 1
remaining = remaining.replace(old_gap, new_gap)
review = [
    'The independence lemma applies the actual quotient projection to every finite real relation, forces all lift coefficients to zero using projected independence, then forces all kernel coefficients to zero. It includes empty index types and makes no dimension or lattice assumptions.',
    'Original central lattice columns are embedded by the actual injective center subtype. Their actual quotient projection is zero. The extension uses actual chosen original Gamma logarithmic lifts with their previously proved exact projection identities; no arbitrary quotient section is substituted.',
    'The strengthened center extension retains the original ordered product, actual Gamma integer-parameter criterion and rational span membership while adding genuine real linear independence. The global theorem discharges the quotient existence premise recursively by strict decrease of actual real model dimension, with genuine quotient discreteness and cocompactness. No analytic equidistribution premise is present.',
    'The trivial original group base gives a zero-dimensional model via actual native exponential injectivity. The primed independent-cardinality basis construction covers this empty basis as well as nontrivial dimensions. The chosen basis is fixed from Gamma and the original Lie model before any functional or polynomial data.',
    'Real independence restricted to Q proves independence of the original rational columns. The previously proved actual rational rank equality gives a complete basis of the original rational log span, not an enlarged ambient rational space.',
    'Coordinate compatibility follows by applying actual real basis reconstruction to actual rational basis reconstruction and the rational scalar cast identity. Both directions of the rational-coordinate membership criterion are proved. Rational adjoint differential coefficients use already-proved closure of the original rational span; that differential equals the original native Lie bracket by retained proofs.',
    'Functional integrality on every chosen column follows from its actual exponential lying in the original Gamma and actual Log(exp(v))=v. Integer uniqueness uses injectivity of the real integer cast. The zero test uses the genuine spanning real basis.',
    'The final grid theorem is conditional on the displayed Euclidean bound on all actual basis evaluations and on an actual horizontal Gamma-integral functional. It does not assert existence of such a functional, a coefficient bound from non-equidistribution, a filtration-adapted horizontal subset, or quantitative Leibman. No arbitrary free integer coordinates are substituted.',
    'The ordered exponential map is proved bijective and has an exact original lattice membership predicate. No smooth inverse, full filtration adaptation, complete Malcev basis in the required sense, full StrongConjecture, independent kernel replay, external review, public repository, PR or prize submission is claimed.',
    'Focused autoImplicit=false checks, full build, retained source hashes and standard-only selected transitive axiom reports are author-side verification. All six pinned primary paper sections are compared.'
]
src = Path(old+'-audit.py').read_text(encoding='utf-8')
src = re.sub(r'^PREFIX = .*$', 'PREFIX = '+repr(prefix), src, count=1, flags=re.M)
src = re.sub(r'^OLD = .*$', 'OLD = '+repr(old), src, count=1, flags=re.M)
a = src.index('MODULES = '); b = src.index('\ndef declarations():', a)
src = src[:a]+f'MODULES = {modules!r}\nCOMPONENTS = {components!r}\nREMAINING = {remaining!r}\n'+src[b:]
a = src.index('        application_review=COMPONENTS+'); b = src.index('\n        verified=summary', a)
src = src[:a]+f'        application_review=COMPONENTS+{review!r}+[REMAINING],'+src[b:]
src = re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions actual original ordered lattice real and rational bases and integral evaluation coordinates; smooth inverse, full filtration adaptation and quantitative character existence remain open'", src)
Path(prefix+'-audit.py').write_text(src, encoding='utf-8')
print('Prepared actual ordered lattice basis audit for', len(modules), 'modules.')
