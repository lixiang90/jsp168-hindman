from pathlib import Path
import json
prefix='round-alignment-complete-cube-test-approximation'
manifest=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert manifest['last_round']['review_file']==prefix+'-review.json'
summary=json.loads(Path(prefix+'-checks.json').read_text(encoding='utf-8'))
p=Path('NATIVE-ORIGINAL-ROUGH-PROPORTION-CONTINUATION.txt')
s=p.read_text(encoding='utf-8')
s=s.replace('Continuation after round-alignment-original-face-probability','Continuation after '+prefix,1)
completed="""COMPLETE ORIGINAL CUBE TEST APPROXIMATION, NOW PROVED:
FinitePiLipschitzProducts defines literal coordinate-observer products and
PROVES their complex submodule span is a genuine star algebra on the FULL
product space. Multiplication/conjugation are handled by original Lipschitz
coordinate algebra and actual span inductions. No new instances or axioms.
FinitePiLipschitzProductDensity proves coordinate products separate EVERY
full product point via a single original coordinate observer and ones at
other coordinates. Complex Stone-Weierstrass gives genuine sup-norm density
in ALL continuous complex cube tests, including the empty-coordinate case.
FinitePiProductLinearApproximation gives an actual FINITE list of retained
complex coefficients and original coordinate Lipschitz observers for EVERY
span element. Any COMPACT test family has ONE finite span approximant list.
AlignmentOriginalContinuousCubeMean defines literal original cube reading
tuples and arbitrary continuous cube-test means. Product means equal EXACTLY
the registered ORIGINAL product cube mean. Approximation controls BOTH
original and own-face means with original boxes/residues/normalization;
empty grids preserve algebraic zero. eta/4 approximation forces eta/2
approximant face failure from a complete-test eta failure.
AlignmentOriginalCubeTestApproximation instantiates the COMPLETE original
numerical bounded/Lipschitz cube test class on the actual product of original
quotient metrics. Actual native compactness gives compactness and ONE fixed
finite span approximant list BEFORE source/box/residue/sample choices.
FinitePiProductLinearMeans proves EXACT finite coefficient combination of
original finite-mass means. AlignmentOriginalCubeProductLinearMean proves
complete-test span approximant mean equals its retained coefficient finite
combination of registered ORIGINAL product cube means.
Complete-test posterior/global probabilities still need common finite
coordinate-observer/coefficient budgets and finite-sum error transfer below.

"""
s=s.replace('NEXT MAIN ROUTE:\n',completed+'NEXT MAIN ROUTE:\n',1)
a=s.index('1. Complete marginal cube test interface / countable diagonal / local limits.')
z=s.index('2. Separate GTZ interval Gowers correlation inverse',a)
s=s[:a]+"""1. Transfer product face probabilities to COMPLETE tests, then diagonal/limits.
   Product face posterior/global caps and prescribed positive-set supported
   selection are PROVED. FULL continuous cube test product-span density,
   compact uniform finite approximation, explicit retained coefficient and
   coordinate observer lists, literal complete-test means, exact finite
   combinations of ORIGINAL product means and two-sided sup-error transfer
   are now PROVED. Do not reconstruct those layers.
   Use AlignmentOriginalCubeTestApproximation at eta/4 and obtain fixed P.
   Use finite_pi_product_span_list_representation for each G in P to choose
   terms(G) BEFORE source/endpoints. Collect ALL original coordinate observers
   from every finite terms list into actual finite observer lists at each nu.
   Derive positive COMMON B(nu) and L(nu) from retained observer norms and
   actual Lipschitz witnesses, with no numeric bound on projections/actions.
   R=1+sum_{G in P} sum_{term in terms(G)} norm(term.coefficient) is a fixed
   positive coefficient budget. Each product face error < eta/(2R) controls
   its finite-combination error below eta/2 by original mean linearity and
   norm triangle. Complete-test failure eta forces approximant error >=eta/2
   by eta/4 approximation, contradiction. Exact native product means/face
   slots and original key/source dependencies remain unchanged.
   The existing ALL original product observer/zero-one profile/own-face
   failure cap with these fixed B/L and tolerance supplies COMPLETE marginal
   test-class posterior/global caps. All approximant/budget choices precede
   source/sampled tuple and every original endpoint/residue/observer.
   Then original integer modulus, dimension <=s+1, target, endpoint/side/test
   bounds and tolerance enumeration: actual finite-prefix caps, supported
   selection in prescribed positive-mass sets, SlowStageDiagonal yields ONE
   countable simultaneous sequence. Preserve original model/master choices;
   unexposed-factor-dependent source selection remains unlicensed.
   Then genuine local cube law limits/cosets and own-face symmetry through
   s+1, face lift, full Alignment, positive distinct rapid common-color FS/FP.

"""+s[z:]
s=s[:s.index('LATEST TERMINAL AUDIT,')]+ 'LATEST TERMINAL AUDIT, 2026-10-14: '+prefix+'.\n'+json.dumps(summary,indent=2)+'\n'
s+='This goal turn added '+str(manifest['last_round']['new_module_count'])+' modules, '+str(summary['new_theorems'])+' theorems and '+str(summary['new_definitions'])+' definitions in one terminal author audit round.\n'
s+='Every prior registered proof and axiom set is unchanged. No audit/compiler process remains active after terminal completion.\n'
s+=manifest['last_round']['remaining']+'\n'
p.write_text(s,encoding='utf-8')
print(prefix)
