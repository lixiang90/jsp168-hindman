from pathlib import Path
import re

prefix='round-rational-taylor-descent'
modules=['Hindman168/NativeRationalTaylorCoordinates.lean',
         'Hindman168/NativeRationalTaylorLevelDescent.lean']
components=[
 'The SAME actual native ordered Taylor constructors now work for EVERY genuine NativeRationalLieFiltration D ell. All actual residuals retain that rational filtration, gain true initial integer zeros, and the genuine terminal layer ell+1 makes the final residual zero at EVERY real input. Actual ordered representation and every coefficient membership in the ORIGINAL exponential filtered group layer are derived, with no Taylor, inverse or factorization premise.',
 'For EACH actual level j>=2, a rational functional killing the original next layer and all original positive bracket terms with indices summing to j constructs a genuine SINGLE-LEVEL kernel filtration. ONLY layer j changes. ALL other positive layers, ambient original group, original lattice and terminal index remain literal. Initial layers, antitone nesting, all bracket pairs INCLUDING zero indices, actual lattice rationality and terminality are proved.',
 'A genuine nonzero value of the selected functional ON THE ORIGINAL changed layer proves STRICT actual finrank drop at that layer. The sum of ALL positive original layer dimensions through the genuine terminal index STRICTLY decreases. This is genuine finite-descent geometry; source correction/adaptation after correction, character production, level-one native subgroup descent and sequential factorization are not assumed or asserted.'
]
remaining=('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
 'Original all-target linear/cube identities, original lower-central adaptation and complete ordered Taylor coordinates remain proved. The same Taylor constructors now have COMPLETE arbitrary genuine rational-filtration representation and actual group-layer memberships; exact j>=2 single-level rational kernel geometry and STRICT total positive-layer dimension decrease are proved. '
 'Remaining: actual sequential rational level characters and bounded-error/integer decomposition, rational pivot and j=1 original native subgroup descent; genuine left/right binomial source corrections and AGGREGATED coefficient adaptation to the new SINGLE-LEVEL filtration; finite sequential descent with ONE filtration and all rational-character irrationality; actual bounded smooth-factor limits and sequence-selected bounded rational period; local cube-Haar laws through ORIGINAL s+1, sequence-before-locality limits, projected Haar face invariance/full-support coset symmetry and actual joint lifts/full Alignment; separate arbitrary-input GTZ interval Gowers LINEAR nilsequence inverse at sufficient native step; final positive distinct rapidly separated SAME-color nonempty FS AND FP. '
 'The new descent geometry assumes only its explicit geometric rational/bracket/next-layer/nonzero conditions; they must be derived for actual selected level characters. No corrected-source/factorization/Haar oracle is introduced. Author checks are not independent kernel replay or external peer review. No unavoidable obstruction, explicit delta-power law or other-marginal invariance is claimed. Public repository/PR/prize milestone not reached.')
src=Path('round-original-linear-cube-audit.py').read_text(encoding='utf-8')
src=src.replace('round-original-linear-cube',prefix)
src=src.replace("OLD='round-native-complete-cube-probability'","OLD='round-original-linear-cube'")
src=re.sub(r'^MODULES=.*$','MODULES='+repr(modules),src,flags=re.M)
src=re.sub(r'^COMPONENTS=.*$','COMPONENTS='+repr(components),src,flags=re.M)
src=re.sub(r'^REMAINING=.*$','REMAINING='+repr(remaining),src,flags=re.M)
Path(prefix+'-audit.py').write_text(src,encoding='utf-8')
review='''JSP-000168 / Erdos #172 -- author mathematical review, 2026-10-14
Verdict: Partial overall coverage; PROGRESS. StrongConjecture UNPROVED.
Goal ACTIVE; no unavoidable obstruction established.
Author checks are not independent kernel replay or external peer review.

Primary source: OpenAI math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
07_cube_limits.tex 246--258 (ordered Taylor coordinates), 293--313
(single-layer rational kernel filtration and finite descent).

1. Rational Taylor closure. The SAME actual native correction, residual and
ordered-product definitions from the prior round are used without editing
them. Their true all-real group identities and integer zeros are independent
of the chosen filtration. Proved original rational product weights supply
all genuine residual weights. Antitone quotient-dual initial-zero arguments
apply to each actual layer, including stage zero via weighted evaluation.
The terminal index is ell, not silently the ambient nilpotence bound s.
For the original section-7 starting filtration ell=s, so no original step or
cube dimension is enlarged. Every coefficient's actual group-layer membership
is its genuine exponential image; no new group layer is supplied as a premise.
Rationality is geometric data only; no analytic property is a field of F.

2. Single-layer descent. At j>=2, the new layer function is EXACTLY F_j
intersect ker(phi) at index j, and F_k at every other index. Nesting into
the next layer uses phi's proved annihilation of F_(j+1). Nesting into
the previous layer follows from literal inclusion in F_j. No other layer
is intersected with a kernel, unlike the older nonlinear inverse filtration.
The original initial full layers and original terminal index are unchanged.

3. All bracket indices. If a+b differs from j, old bracket membership suffices.
If a+b=j with a,b>0, the original level-character bracket annihilation input
proves kernel membership. If a=0, use F_0=F_1=top and the OLD bracket at
(1,j), which belongs to F_(j+1) and is killed by phi. The b=0 case uses
(j,1). Thus no missing zero-index bracket or hidden ideal premise remains.

4. Rationality. The actual original lattice rational span is retained.
Explicit rational values of phi on that span imply rational restricted
kernel membership by the previously proved rational span theorem. This
global rational extension condition is EXPLICIT. A character initially
defined only on F_j must still be extended and checked in the future actual
character construction; this geometry theorem does not claim to derive
that extension or a source character automatically.

5. Strict dimension. A genuine z in the actual F_j with phi(z) nonzero
proves F_j intersect ker(phi) is a proper subspace, hence strict finrank
decrease. All other layers are unchanged or included in their originals.
For 2<=j<=ell, finite-sum strict monotonicity at that actual j proves the
sum of every positive layer dimension strictly decreases. No strictness
is claimed for a zero character or a changed level outside the terminal
dimension list. This proves the finite-descent MEASURE, not a completed
sequential induction or character extraction.

6. Boundary and proof trust. Taylor closure includes ell=0 and arbitrary
original native groups. Descent is explicitly j>=2, covering neither the
j=1 ambient subgroup change nor source polynomial correction. Only the
original local smoothness instance is enabled; no new instance, structure,
axiom, sorry, admit, native computation shortcut, heartbeat change or kernel
bypass is introduced. Old proof hashes and every retained selected axiom
set are compared by the terminal audit.

7. Coverage. The actual corrected-source coefficient adaptation to the NEW
single-layer filtration is NOT proved. Its aggregate coefficient cancellation
must be established, then converted to a genuine collected weighted source;
termwise cancellation must not be inferred from a character value or circle
norm. Actual level-one subgroup descent, simultaneous all-character sequential
descent, rational periodicity, convergent smooth factors, local cube-Haar laws,
coset face symmetries, joint lifts/Alignment, the distinct arbitrary-input GTZ
Gowers LINEAR nilsequence inverse and final positive same-color FS AND FP
remain unproved. There is no unavoidable mathematical obstruction.
'''
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
print('Prepared rational Taylor / single-layer descent author audit.')
