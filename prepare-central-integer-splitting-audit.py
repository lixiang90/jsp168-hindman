from pathlib import Path
import json
import re

prefix = 'round-central-integer-splitting'
old = 'round-native-smooth-character-coordinates'
modules = ['Hindman168/'+m+'.lean' for m in [
    'IntegerSubspaceQuotient', 'IntegerSubspaceSplit', 'NativeCenterLayerIntegerSplit']]
components = [
    'For any actual integer submodule of a real vector space and any actual real subspace, the quotient by their integer intersection has a constructed injective integer linear map into the real quotient. It is torsion-free, and is free when the original integer module is finitely generated.',
    'The original integer quotient map has an actual integer linear right inverse by the proved finite free quotient and projectivity. Its image is an integer direct complement to the actual integer intersection. This construction does not substitute a rational vector-space complement for an integer complement.',
    'For the genuine original central logarithmic lattice and every actual original lower-central layer, actual integer intersection membership is exactly original layer membership of the original vector. The actual integer quotient is free and has an integer direct complement inside the genuine original central lattice. The original finite lattice basis discharges finite generation; no additive lattice of full Log Gamma is assumed.'
]
remaining = json.loads(Path('verification-manifest.json').read_text())['last_round']['remaining']
gap = 'Full adaptation of the original ordered lattice basis to all specified filtration layers remains unproved.'
assert remaining.count(gap) == 1
remaining = remaining.replace(gap,
    'Integer quotients of the genuine original central logarithmic lattice by each original lower-central-layer intersection are now proved free with actual integer complements. This provides the arithmetic splitting for central flag adaptation. A simultaneously adapted integer basis for the whole central flag, its smooth ordered center extension and full prescribed filtration adaptation of the original ordered lattice basis remain unproved.')
review = [
    'The integer intersection is literally the preimage of the original real subspace under the actual original integer-submodule inclusion. The quotient embedding is constructed by the real quotient projection and actual integer quotient lift; its kernel is proved zero using actual quotient representatives. No discreteness or rationality premise is needed for this elementary statement.',
    'Torsion-freeness is pulled back along the proved actual injective quotient map from the real quotient as an integer module. Finite generation of the integer quotient is supplied by the actual surjective original quotient map. The standard PID theorem for finitely generated torsion-free integer modules proves freeness, including the zero-dimensional and trivial-quotient cases.',
    'The split uses the actual integer-linear scalar restriction of the original quotient projection, preserving its literal function. This avoids a module-instance diamond between canonical integer scalar structures and inherited quotient scalar structures. No algebraic map is replaced by a freely chosen function; the actual right-inverse identity is proved as an equality of integer linear maps.',
    'For the right-inverse image Q, actual quotient evaluation proves intersection disjointness. Every original integer vector x is explicitly decomposed as x-s(pi(x)) plus s(pi(x)), with the first term in the actual integer intersection. These prove IsCompl over Z, not over Q or R.',
    'The native application uses the genuine original center logarithmic lattice, whose additive lattice status was previously proved using the actual original commuting exponential laws. The layer intersection is the comap of the actual original real Lie lower-central layer through the actual center inclusion. The chosen original integer lattice basis proves Module.Finite Z L; no formal full Log Gamma lattice is introduced.',
    'Each layer receives an integer complement, but their choices are not claimed compatible. No simultaneous central flag basis, full ordered basis adaptation, paper horizontal size identification, quantitative equidistribution input, full StrongConjecture, unavoidable obstruction, independent kernel replay, public repository, PR or prize submission is asserted.',
    'All retained registered proof sources and axiom sets are checked unchanged. Focused autoImplicit=false checks, full build, standard-only selected axiom reports and all six pinned primary sections are author-side verification.'
]
src = Path(old+'-audit.py').read_text(encoding='utf-8')
src = re.sub(r'^PREFIX = .*$', 'PREFIX = '+repr(prefix), src, count=1, flags=re.M)
src = re.sub(r'^OLD = .*$', 'OLD = '+repr(old), src, count=1, flags=re.M)
a = src.index('MODULES = '); b = src.index('\ndef declarations():', a)
src = src[:a]+f'MODULES = {modules!r}\nCOMPONENTS = {components!r}\nREMAINING = {remaining!r}\n'+src[b:]
a = src.index('        application_review=COMPONENTS+'); b = src.index('\n        verified=summary', a)
src = src[:a]+f'        application_review=COMPONENTS+{review!r}+[REMAINING],'+src[b:]
src = re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions actual central integer-layer quotients and complements for filtration-adapted lattice basis construction; simultaneous flag adaptation and quantitative existence remain open'", src)
Path(prefix+'-audit.py').write_text(src, encoding='utf-8')
print('Prepared actual central integer splitting audit for', len(modules), 'modules.')
