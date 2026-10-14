from pathlib import Path
import json
import re

prefix = 'round-ordered-central-flag'
old = 'round-central-flag-basis'
modules = ['Hindman168/'+m+'.lean' for m in [
    'FiniteFlagOrder', 'OrderedFlagBasis', 'NativeCenterOrderedFlagBasis',
    'OrderedFlagDimensions', 'NativeCenterOrderedFlagCoordinates',
    'KernelContainedLayerLatticeLift', 'IntegerLayerLiftCounterexample']]
components = [
    'Finite decreasing flags can be ordered by actual membership depth. The actual sorting permutation makes every layer an upper set of finite indices, whose actual complement cardinality is a proved suffix start. Reindexing an actual simultaneously adapted basis preserves its layer spans and gives actual consecutive suffix blocks.',
    'The genuine original central integer lattice has a chosen ordered basis with actual consecutive suffix blocks for every original lower-central layer index. Its same-column real basis has the same actual layer spans. Suffix starts are monotone and equal the actual central layer codimensions, including zero-dimensional and terminal cases.',
    'For the exact chosen ordered central basis, original Gamma exponential membership is equivalent to integer real coordinates, and original Lie lower-central membership is equivalent to zero coordinates on the actual prefix preceding the corresponding suffix start.',
    'For an actual group homomorphism whose kernel lies in the specified layer, the image of the original lattice/layer intersection equals the intersection of the two images, and actual relative original lattice-layer lifts are constructed. No kernel containment is assumed for arbitrary full-center layers.',
    'A concrete integer plane module, a specified rational real line x=2y and first-coordinate projection provide a kernel-checked failure of unconditional relative lattice-layer lifting: 1 belongs to both separate images but not the intersection image. This audits a missing construction hypothesis; it is not a counterexample or unavoidable obstruction to the original nilpotent-group prize theorem.'
]
remaining = json.loads(Path('verification-manifest.json').read_text())['last_round']['remaining']
gap = 'Consecutive ordered index blocks for the flag, insertion of this basis into the full original smooth ordered extension, relative quotient lattice-layer lift compatibility and full prescribed filtration adaptation of the original ordered lattice basis remain unproved.'
assert remaining.count(gap) == 1
remaining = remaining.replace(gap,
    'A separately chosen ordered genuine original central integer basis and its same-column real basis now have consecutive suffix blocks for every original lower-central layer. Their starts are monotone and equal the actual layer codimensions, with exact original Gamma integer coordinates and prefix-zero layer coordinates. Insertion of this ordered basis into the full original smooth ordered extension and full prescribed filtration adaptation remain unproved. Relative lattice-layer images and lifts are proved when the actual quotient kernel is contained in the layer; a concrete integer-plane rational-line example disproves unconditional lifting. The actual full-center lift condition is not discharged for arbitrary original lower-central layers. Use a compatible rational central ideal or prove the actual relative lattice-image condition before claiming full adaptation.')
review = [
    'Membership depth is the cardinality of the actual finite set of layers containing a given vector. Antitonicity proves membership in layer j iff j is smaller than that depth, by explicit inclusions of Fin Iic/Iio sets. The actual Tuple.sort permutation orders this natural depth. No order is inferred from a merely arbitrary Fin reindexing.',
    'Every sorted membership predicate is upper. Its actual false-index cardinality is proved a threshold: membership iff threshold is at most the index. The proof uses Iio/Iic cardinalities and works also for empty, full and zero-size flags. Reindexing the actual basis by the inverse sorting permutation retains every layer span and makes it a literal suffix span.',
    'The native construction applies the finite ordering theorem to the actual chosen central integer basis and actual integer lower-central intersections through nilpotencyClass(G)+1. Natural indices are reduced by min(j,class); after the class actual layers are bottom by the original nilpotency theorem and antitonicity. The same ordered basis and chosen starts handle all natural indices.',
    'The same-column real basis comes from the actual chosen ordered integer lattice basis. The proved actual central integer intersection real-span equality transfers its suffix span to the actual real layer. Real coordinate integrality reconstructs original lattice membership. Actual basis-support coordinates prove the prefix-zero criterion; no equality with earlier basis choices or retained full ordered-group basis is asserted.',
    'The suffix dimension theorem restricts the original independent basis to the actual suffix subtype, proves its image equals the original suffix image, and applies the actual independent-span cardinality theorem. Fin interval cardinalities give n-t, including t>=n. Native starts are within dimension; the actual suffix span then proves start equals actual layer codimension. Native antitonicity and a basis column at the later start prove start monotonicity.',
    'Kernel-contained relative lifting uses actual group-image representatives a in Gamma and b in the layer. Their equal projections put a*b^-1 in the actual kernel; containment proves a in the layer. This proves the actual intersection-image equality and extracts an original Gamma/layer lift. The kernel containment hypothesis is explicit and is not silently discharged for full-center quotients.',
    'The reviewed counterexample is the literal integer pair module and literal real linear-map kernel x-2y. First projection sends an integer vector to 1 and sends the actual line vector (1,1/2) to 1. Any common original vector with first projection 1 would have integer coordinates a,b satisfying a=1 and a=2b, contradicted by integer arithmetic. All projections and image memberships are actual maps. This does not exhibit a failure of the original native lower-central theorem, nor rule out compatible smaller central ideals.',
    'The original complete prize theorem, analytic quantitative Leibman existence/bounds, full lattice filtration adaptation, independent kernel replay, public repository, PR and award application remain unproved/unperformed. Prior registered proof sources and selected axiom sets are hash-retained unchanged.'
]
src = Path(old+'-audit.py').read_text(encoding='utf-8')
src = re.sub(r'^PREFIX = .*$', 'PREFIX = '+repr(prefix), src, count=1, flags=re.M)
src = re.sub(r'^OLD = .*$', 'OLD = '+repr(old), src, count=1, flags=re.M)
a = src.index('MODULES = '); b = src.index('\ndef declarations():', a)
src = src[:a]+f'MODULES = {modules!r}\nCOMPONENTS = {components!r}\nREMAINING = {remaining!r}\n'+src[b:]
a = src.index('        application_review=COMPONENTS+'); b = src.index('\n        verified=summary', a)
src = src[:a]+f'        application_review=COMPONENTS+{review!r}+[REMAINING],'+src[b:]
src = re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions original ordered central suffix flag and dimensions; actual relative lifting conditions and counterexample audit; full filtration adaptation and quantitative existence open'", src)
Path(prefix+'-audit.py').write_text(src, encoding='utf-8')
print('Prepared ordered central flag and relative lifting audit for', len(modules), 'modules.')
