from pathlib import Path
import json, re

prefix = 'round-native-lattice-smooth-coordinates'
old = 'round-native-lattice-ordered-basis'
modules = ['Hindman168/'+m+'.lean' for m in [
    'QuotientSectionRetraction', 'NativeOrderedExponentialSmooth',
    'NativeCenterCoordinateRecovery', 'NativeCenterPairSmoothInverse',
    'FiniteCoordinateSplitSmooth', 'NativeOrderedSmoothInverse',
    'NativeCenterOrderedSmoothBasisExtension', 'NativeLatticeOrderedSmoothBasis',
    'NativeLatticeOrderedDiffeomorph', 'NativeLatticeOrderedSmoothRationalBasis',
    'NativeLatticeOrderedSmoothBasisCoordinates']]
components = [
    'Every actual finite-dimensional closed real submodule has a constructed continuous linear retraction fixing its genuine subtype vectors. It uses the already-constructed actual quotient section, not an assumed projection. Every finite original ordered exponential product is smooth, with the literal original product order retained.',
    'A global smooth original center-coordinate recovery function is constructed from the genuine original logarithm, an actual center-model retraction, and the original central lattice basis. It recovers the original center coordinates and reconstructs every genuinely central original group element.',
    'For actual quotient ordered coordinates with a smooth right inverse and the genuine original lifted columns, the original pair-coordinate product has a constructed smooth two-sided inverse. The proof uses original quotient coordinates and the genuine central residual lift-inverse times g. Actual finite splitting is upgraded to a continuous linear equivalence, preserving the exact original concatenation order.',
    'Strengthened actual native center dimension induction now proves existence of original ordered lattice coordinates with independent rational columns, exact original Gamma/integer parameter membership and a genuine smooth two-sided inverse. The actual finite ordered product is smooth as well, so a fixed original lattice-coordinate Diffeomorph is constructed, including the zero-dimensional base.',
    'For the fixed smooth ordered real lattice basis, its identical original columns also form an actual rational basis of the original rational logarithmic span. Its actual rational and real coordinate square commutes, membership in the original rational span is exactly coordinate rationality, and original adjoint differential structure constants are rational. These statements refer to the same fixed basis used in the constructed Diffeomorph.'
]
remaining = json.loads(Path('verification-manifest.json').read_text())['last_round']['remaining']
old_gap = 'Smooth inverse and adaptation of the ordered lattice basis to all specified filtration layers remain unproved.'
new_gap = 'A strengthened original center induction now constructs a fixed original ordered lattice real basis with a genuine global smooth two-sided inverse and packages its ordered exponential map as an actual Diffeomorph. That same smooth basis has an identical-column rational basis of the original logarithmic span and rational original adjoint differential structure constants. Full adaptation of the original ordered lattice basis to all specified filtration layers remains unproved. This strengthened smooth basis is chosen separately from the earlier basis-only choice; their literal equality is not asserted.'
assert remaining.count(old_gap) == 1
remaining = remaining.replace(old_gap, new_gap)
review = [
    'The submodule retraction is the actual codomain restriction of x minus s(pi(x)); its membership proof uses the actual quotient-section right inverse. Its subtype identity is proved. Finite dimension gives genuine continuity. No original Log Gamma is treated as an additive lattice.',
    'The finite-product smoothness proof inducts over the actual ordered list and then specializes to the actual List.ofFn of original exponentials. No noncommutative product is replaced by an unordered finset product. All finite coordinate functions and real scalar multiplications are actual smooth maps.',
    'The original center recovery function is defined on every original group element, but its reconstruction law is explicitly restricted to genuinely central elements. The true original logarithm is used. The central recovery identity follows from the proved original exponential/log inverse and the actual retraction subtype identity.',
    'The pair inverse uses a(g)=rQ(q(g)) and z(g)=orderedExp(u,a(g))^{-1}*g. The exact original lifted-column projection identities and the quotient right inverse prove q(z(g))=1, so the residual is actually central. Center recovery reconstructs z(g), proving the original right inverse. Genuine original pair-product injectivity then proves the other inverse identity. Smoothness follows from actual original quotient projection, ordered products, inversion, multiplication and center recovery.',
    'The pair inverse theorem has a quotient smooth right-inverse premise and actual pair bijectivity premise. The final original existence theorem DISCHARGES both using original generator lifts, the earlier original pair coordinate theorem and actual center quotient dimension induction. No smooth inverse is inferred merely from bijectivity.',
    'The actual finite split continuous linear equivalence has literal original finite split toFun and Fin.append inverse. It carries the constructed pair inverse to the actual concatenated ordered original coordinate map. Both inverse identities and smoothness are separately proved.',
    'The strengthened zero-dimensional base uses the actual original exponential injectivity to make the original real model subsingleton, constructs the empty independent vector family, verifies exact original lattice membership and supplies a smooth constant inverse. The recursive step uses actual strict center quotient dimension decrease, actual quotient Lie model and actual original lattice-image discreteness and cocompactness.',
    'The fixed smooth basis is chosen from the strengthened proved existence theorem. Its actual ordered product and chosen smooth inverse form a genuine Diffeomorph, whose membership in the original Gamma is exactly all integer parameters. The actual real basis columns have original Gamma exponentials and belong to the original rational logarithmic span.',
    'The earlier basis-only Classical.choose is not identified with the strengthened smooth basis Classical.choose. The newly registered rational basis and coordinate proofs use the SAME strengthened smooth basis as the Diffeomorph, preventing an unjustified transfer between separate choices. Real independence restricted to Q plus actual rational rank equality gives the genuine rational basis.',
    'No full prescribed filtration adaptation, identification of the filtration-adapted horizontal coefficient norm, actual quantitative character existence or modular coefficient bound, full StrongConjecture, unavoidable obstruction, public repository, PR or prize submission is claimed.',
    'Focused autoImplicit=false checks, full build, retained proof hashes and standard-only selected transitive axiom reports are author-side verification. All six pinned primary paper sections are compared; no independent replay or external review is claimed.'
]
src = Path(old+'-audit.py').read_text(encoding='utf-8')
src = re.sub(r'^PREFIX = .*$', 'PREFIX = '+repr(prefix), src, count=1, flags=re.M)
src = re.sub(r'^OLD = .*$', 'OLD = '+repr(old), src, count=1, flags=re.M)
a = src.index('MODULES = '); b = src.index('\ndef declarations():', a)
src = src[:a]+f'MODULES = {modules!r}\nCOMPONENTS = {components!r}\nREMAINING = {remaining!r}\n'+src[b:]
a = src.index('        application_review=COMPONENTS+'); b = src.index('\n        verified=summary', a)
src = src[:a]+f'        application_review=COMPONENTS+{review!r}+[REMAINING],'+src[b:]
src = re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions genuine original ordered lattice Diffeomorph by native center dimension induction and its compatible rational basis; full filtration adaptation and quantitative existence remain open'", src)
Path(prefix+'-audit.py').write_text(src, encoding='utf-8')
print('Prepared genuine original smooth coordinate audit for', len(modules), 'modules.')
