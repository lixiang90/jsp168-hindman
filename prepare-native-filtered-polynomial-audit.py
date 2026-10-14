from pathlib import Path
import json
import re

PREFIX = 'round-rough-native-filtered-polynomial'
OLD = 'round-rough-stretched-filtration-weighted-difference'
MODULES = ['Hindman168/'+m+'.lean' for m in [
    'RoughNativeStretchedLattice', 'RoughParametricWeightedDegree',
    'RoughParametricEvaluation', 'RoughParametricWeightedPicard',
    'RoughParametricBilinearPerturbation', 'RoughParametricAdPerturbation',
    'RoughParametricDefectPerturbation', 'RoughParametricFieldPerturbation',
    'RoughParametricPicardPerturbation', 'RoughNativeGroupDifferencePolynomial',
    'RoughFilteredPolynomialRestriction', 'RoughNativePolynomialFiltered',
    'RoughVectorParameterSpecialization', 'RoughNativeJointPolynomialFiltered']]
COMPONENTS = [
    'The actual stretched native Lie layers are rational relative to the original specified lattice log span. Their actual lattice-intersection quotients are compact and metrizable, and their actual quotient inclusions are closed embeddings with compact orbits, by exact original group/Lie equality.',
    'The sufficient spatial weighted coefficient condition extends to actual finite parametric curves. It is stable under append, finite sum, endpoint, rational scale, time primitive and brackets. Actual Picard, defect and field operations preserve each base weighted offset.',
    'Actual parametric evaluations satisfy exact singleton, append, finite sum, bracket, scale, endpoint and Bochner primitive laws. Primitive perturbations equal the actual difference of the two original primitives, using continuous polynomial integrability.',
    'Finite constructive bilinear, iterated adjoint, defect and field perturbation polynomials evaluate exactly to the respective new-minus-old actual operations. Every perturbation remains at its supplied higher weighted offset while base operations stay at their base offset.',
    'A finite constructive Picard perturbation has exact new-minus-old actual Picard evaluation and retains the higher weighted offset through every finite iteration. This uses the existing original native Picard product construction rather than an assumed formal BCH series.',
    'The actual native group difference logarithm has a constructed vector polynomial representation at one higher weighted offset. Its baseline endpoint vanishes by original exponential inverse and global-logarithm identities, thereby rigorously removing all terms with no perturbation.',
    'Iterated actual group differences have constructed logarithm polynomials with offset increased by the actual list length. Every bounded-degree original logarithm polynomial exponentiates to a polynomial map for the actual stretched group filtration, over real coordinates and over integer coordinates.',
    'Actual additive homomorphism restriction preserves all iterated group differences and filtered polynomiality. Fixing the scalar parameter in an actual joint vector polynomial preserves its spatial degree and exact evaluation; joint integer affine sampling is filtered polynomial with fixed positive stretch max(1,q), including degree zero.'
]
previous = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))['last_round']['remaining']
REMAINING = previous.replace(
    'The actual stretched group filtration, its original native Lie-layer equality and topology, native weighted brackets, initial bounded-degree coefficient condition and actual zero-filtered ordinary weighted differences are now proved. Actual native BCH cancellation and weighted group difference membership remain open; the sufficient termwise condition has not yet been propagated through the full BCH difference. Rationality of the actual stretched layers relative to the original lattice must still be assembled from actual rational log spans.',
    'The actual stretched rational connected filtration and polynomiality of bounded-degree native logarithm polynomials are now proved, including actual lattice compact quotients, weighted native Picard perturbation, baseline BCH cancellation, iterated group differences and joint integer affine sampling with fixed positive stretch max(1,q). No bound on coefficients is imposed. An explicit degree bound uniform over all iterated difference lengths has not yet been extracted from this representation; actual filtered membership at every length is proved. The equal-side quantitative Leibman theorem, its adapted rational basis and uniformly finite nonzero character construction remain open analytic inputs.')
assert REMAINING != previous
REVIEW = [
    'Every group layer, logarithm, exponential, Lie bracket and lattice used is the original native object. The rational layer statement concerns the original rational log span, not an assumed additive Log Gamma lattice.',
    'The termwise weighted condition is sufficient and can be stronger than coefficient membership after cancellation. Starting from an arbitrary degree-D list representation satisfies it, and all constructed perturbation lists retain it.',
    'Bilinear perturbation uses B(dp,q1)+B(p0,dq), which evaluates to B(p1,q1)-B(p0,q0). Both original maps are preserved in the evaluated identity; higher weights are carried only by perturbation inputs.',
    'Finite adjoint, defect powers and Picard perturbations are constructed recursively and their exact evaluation is proved at every spatial point and real time. No unproved BCH formula or cancellation axiom is introduced.',
    'Time primitive preserves the higher spatial weight because it only rescales spatial vectors by rational inverse time degree. Its exact evaluated difference is proved using actual Bochner integral subtraction with continuous finite polynomial integrability.',
    'The native group difference uses unchanged second input -A and actual first-input ordinary difference. The reference product exp(A)*exp(-A) equals one and its original global logarithm is zero. Cancellation is semantic through proved endpoint equality, not an unsupported syntactic list cancellation.',
    'All k-fold actual left group differences are treated by induction on the actual list of shifts. The resulting logarithm representation has weighted offset k, which implies actual exponential membership in the kth group layer. Integer restriction is via an actual additive cast homomorphism.',
    'The stretch is max(1,q) for joint degree q, fixed before every scalar parameter, origin and dilation. Parameter specialization and real affine substitution have exact actual evaluations and do not increase degree. No coefficient bound or positive dilation hypothesis is needed for polynomiality.',
    'This closes the stretched-filtration polynomiality portion of the paper argument. It does not prove quantitative equal-side Leibman or construct its adapted Malcev basis and finite character bound. Uniform ordinary degree of all iterated representations has not been claimed.',
    'Focused autoImplicit=false checks, full build, retained source hashes and selected standard-only axiom reports are author-side verification. All six pinned primary sections are compared; no complete StrongConjecture, independent replay or prize eligibility is claimed.'
]
src = Path(OLD+'-audit.py').read_text(encoding='utf-8')
src = re.sub(r"^PREFIX = .*?$", 'PREFIX = '+repr(PREFIX), src, count=1, flags=re.M)
src = re.sub(r"^OLD = .*?$", 'OLD = '+repr(OLD), src, count=1, flags=re.M)
start = src.index('MODULES = ')
end = src.index('\ndef declarations():', start)
src = src[:start]+f'MODULES = {MODULES!r}\nCOMPONENTS = {COMPONENTS!r}\nREMAINING = {REMAINING!r}\n'+src[end:]
start = src.index('        application_review=COMPONENTS+')
end = src.index('\n        verified=summary', start)
src = src[:start]+f'        application_review=COMPONENTS+{REVIEW!r}+[REMAINING],'+src[end:]
src = re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions actual rational stretched filtration and native weighted Picard/BCH group-difference polynomiality; equal-side quantitative Leibman remains open'", src)
src = src.replace('2026-10-11', '2026-10-12')
Path(PREFIX+'-audit.py').write_text(src, encoding='utf-8')
