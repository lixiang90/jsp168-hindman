from pathlib import Path
import json,re
prefix='round-native-lattice-ordered-coordinates'
old='round-rough-horizontal-coordinate-budget'
modules=['Hindman168/'+m+'.lean' for m in [
'IntegerLatticeCoordinates','GroupKernelCoordinates','NativeCenterLatticeCoordinates',
'NativeCenterOrderedCoordinates','NativeCenterLatticeGeneratorLift','NativeOrderedExponentialCoordinates',
'NativeCenterCoordinateExtension','FiniteCoordinateSplit','NativeOrderedCoordinateAppend',
'NativeCenterOrderedCoordinateExtension','NativeLatticeOrderedCoordinates']]
components=[
'For a genuine original additive Z-lattice the actual real basis coordinates are integral exactly for lattice members. The actual integer basis and actual real basis representations are identified, and synthesis has the same exact membership criterion.',
'The original center lattice has a constructed global real-coordinate homeomorphism onto the actual group center. Its image lies in the original Gamma exactly when all coordinates are integers, and it equals the actual ordered product of original exponential basis factors.',
'An abstract group kernel-coordinate product is injective and surjective under the precise quotient and kernel coordinate hypotheses. Its original lattice membership is equivalent to the two coordinate lattice predicates, provided integral quotient coordinates lift into the original lattice.',
'Every family of actual center-quotient exponential lattice generators has chosen original Gamma representatives whose actual original logarithms lift exactly those quotient vectors and lie in the original rational logarithmic span.',
'Actual ordered original exponential coordinates map exactly to the corresponding actual ordered center-quotient exponential coordinates for every real parameter. Integer parameter products belong to the original Gamma when each original exponential generator belongs to Gamma.',
'The actual center extension constructs ordered original coordinates from quotient coordinates, with global bijectivity and exact integer lattice membership. Finite coordinate splitting and ordered concatenation retain the literal product order and give a single Fin-indexed vector family.',
'Genuine dimension induction through the actual native center quotients proves existence of an ordered original exponential coordinate system for every original native simply connected nilpotent lattice. The number of parameters equals the original real model dimension, the original coordinate map is bijective, and its image is in the original Gamma exactly for integral coordinates. All chosen vector exponentials lie in the actual Gamma and all vectors lie in its actual rational log span.'
]
remaining=json.loads(Path('verification-manifest.json').read_text())['last_round']['remaining']
remaining=remaining.replace('and construct and identify the required full lattice-coordinate Malcev basis.',
'and finish the required Malcev basis and filtration adaptation. Global ordered exponential coordinates of the correct dimension, with bijectivity and exact original Gamma/integer-coordinate correspondence, are now proved by actual center induction. Linear basis independence of the chosen vector family, smooth inverse and adaptation of the ordered basis to all specified filtration layers have not yet been proved; the coordinate existence theorem alone does not discharge those requirements.')
review=[
'The additive lattice coordinate criterion uses an actual Z-basis and its genuine real extension, with both directions proved. Original nonabelian Log Gamma is never treated as an additive Z-lattice; only the genuine center log lattice is.',
'The center coordinate map is a homeomorphism constructed from the actual central real lattice basis and the original center exponential. Its integer membership criterion refers to the original Gamma, not a replaced or enlarged lattice.',
'The ordered central product identity retains the actual finite order and uses original central exponential addition. Each central basis exponential is in the original Gamma and each basis vector is in its actual rational log span.',
'Quotient generator lifts use membership in the actual image Gamma.map q to choose original Gamma representatives. Their actual native logarithms project exactly to the original specified quotient vectors. No arbitrary smooth section is assumed to preserve lattice members.',
'The group kernel-coordinate uniqueness proof projects to recover the quotient coordinate and cancels the original lift to recover the kernel coordinate. Surjectivity uses the actual residual lift inverse times g. The lattice reverse implication first recovers the quotient lattice predicate, then cancels an actual Gamma lift.',
'Ordered coordinate projection uses the genuine native exponential homomorphism theorem for the actual center quotient and preserves every real parameter and the original product order. Integer products use the actual integer-scalar exponential power identity.',
'The extension theorem assumes quotient ordered coordinate bijectivity and its exact lattice membership criterion. The final existence theorem discharges those assumptions recursively by strong induction on actual real model dimension, using the previously proved strict center quotient dimension drop and original quotient lattice discreteness/cocompactness.',
'The trivial group base proves the original model is zero-dimensional by the original exponential injectivity, uses zero coordinates and verifies both bijectivity and exact original lattice membership. Empty index types and zero-dimensional centers are included.',
'The final existence theorem gives the correct number of parameters, original rational vector columns with original lattice exponentials, a bijective ordered coordinate map, and exact Gamma/integer parameter correspondence. It does not yet prove that these columns are a linear basis, a smooth inverse, the full filtration adaptation, or quantitative Leibman. Those remain explicit future work.',
'Focused autoImplicit=false checks, full build, retained source hashes and standard-only selected transitive axiom reports are author-side verification. All six pinned primary sections are compared; no independent replay, full target, public contribution or prize submission is claimed.'
]
src=Path(old+'-audit.py').read_text(encoding='utf-8')
src=re.sub(r'^PREFIX = .*$', 'PREFIX = '+repr(prefix),src,count=1,flags=re.M)
src=re.sub(r'^OLD = .*$', 'OLD = '+repr(old),src,count=1,flags=re.M)
a=src.index('MODULES = ');b=src.index('\ndef declarations():',a)
src=src[:a]+f'MODULES = {modules!r}\nCOMPONENTS = {components!r}\nREMAINING = {remaining!r}\n'+src[b:]
a=src.index('        application_review=COMPONENTS+');b=src.index('\n        verified=summary',a)
src=src[:a]+f'        application_review=COMPONENTS+{review!r}+[REMAINING],'+src[b:]
src=re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions actual original lattice ordered exponential coordinates by native center dimension induction; linear basis and filtration adaptation and quantitative existence remain open'",src)
Path(prefix+'-audit.py').write_text(src,encoding='utf-8')
print('Prepared ordered-coordinate audit engine for',len(modules),'modules.')
