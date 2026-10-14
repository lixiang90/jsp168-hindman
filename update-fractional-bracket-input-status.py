from pathlib import Path
import json

prefix = 'round-native-rational-fractional-bracket-input'
review = json.loads(Path(prefix+'-review.json').read_text(encoding='utf-8'))
manifest = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert manifest['last_round']['review_file'] == prefix+'-review.json'
s = review['verified']
assert s['full_target_proved'] is False
status = f'''JSP-000168 / Erdos #172 -- 2026-10-13

Goal ACTIVE; StrongConjecture UNPROVED; no unavoidable obstruction found.
Verdict: Partial coverage. Full original FS/FP goal and full Lean completeness
for a prize submission remain OPEN. Previous goal turn classified PROGRESS.
Latest audit: {prefix}
{len(review['new_modules'])} new modules, {s['new_theorems']} theorems,
{s['new_definitions']} definitions. Every final verification awaited terminal success.

NOW PROVED / REVIEWED:
'''+ '\n'.join('* '+c for c in review['application_review'][:-1])
status += f'''

VERIFIED:
{s['project_modules']} own modules; {s['pntplus_modules']} attributed PNT+ modules.
{s['build_jobs']} successful full-build jobs; {s['selected_axiom_reports']} selected
standard-axiom reports. Every new module explicitly checked with
-DautoImplicit=false and EMPTY logs. All old registered proof-source hashes
and selected old axiom sets unchanged; only root/import and verification
registries changed. Lean 4.32.2, pinned mathlib/PNT+ and all six pinned
OpenAI sections rechecked. Author checking is NOT independent kernel replay
or external peer review. Exact rational source-slab certificate was executed,
recorded, hash retained and arithmetic checked; it is NOT Lean measure proof.

CURRENT EXACT SCOPE:
The ACTUAL nonzero Fourier signal now gives bounded fractional bracket
parameters with actual beta correction and SAME natural M on SAME actual
refined useful shifts V, at ORIGINAL N scale and positive fixed density.
BOTH original higher P/Q coefficient tables and actual relative character/
operator/original-grid/combined-bound properties survive. General degree
still has FULL desired lower-degree child inverse premise; degree-two input
discharges that premise. Actual bracket alternative itself remains OPEN.

Claim 7.7 case-(ii) ORIGINAL CHARACTER RECONSTRUCTION is now COMPLETE from
an ACTUAL bounded nonzero integer vector with small k dot gamma: true
nonzero/horizontal/operator/original finite grid and BOTH COMPLETE original
raw monomial/Mv-paper-binomial coefficient tables for EVERY positive Unit
multiindex, with one fixed positive natural budget before ALL raw sources.
No child inverse premise is needed for this reconstruction. The vector is
NOT yet extracted from the original signal.

Both Claim 7.7 circle-algebra transformations are PROVED: unrestricted alpha
is adjoined as frequency with coefficient ONE and linear slope ZERO, and
the second correction subtracts an ACTUAL nearest integer. Absolute
nearest-integer residual equals true circle norm. Corrected zeta=r*zeta-k,
beta'=r*beta preserves r times the original circle bracket at NATURAL shifts;
the original-scale error is bounded by |r|*B, for either sign of r.

SOURCE REVIEW FINDING:
The displayed Proposition 5.3 slab-volume bound before (5.10)-(5.11) cannot
be used unchanged. delta=1/100, zeta=100, theta=0 gives norm(100*t)<=1/10
on [0,1], with 101 disjoint clipped intervals of total length 1/5 > 1/200
(the displayed delta/2). Exact rational certificate is recorded in
{prefix}-slab-review.json. This refutes that displayed estimate, NOT the
proposition itself and NOT the complete original goal. Corrected constants
and coefficient-budget-dependent tolerance/neighborhood estimates remain
possible; no unavoidable obstruction established.

A TRUE one-dimensional slab measure bound is formally PROVED:
volume(S)<=ofReal(card(C)*2*eps/z), for z>0 and actual finite integer cover C.
The sufficient delta/2 condition retains card(C). A fixed integer cover for
bounded theta/z and unit-interval t is CONSTRUCTED using actual near-integer
witnesses. This does NOT finish torus boundary/neighborhood/Fubini work.

NEXT:
Prove the full quantitative bracket lemma with CORRECT coefficient/cover
budgets, including negative slopes, torus coordinate-boundary strips,
neighborhood or smooth cutoff estimates, product/Fubini/Haar transport,
actual Lipschitz/unit normalization and genuine torus discrepancy detection.
Available actual primitives: UnitCircleNormBump (including Haar ball bound),
unit_lipschitz_observables_compact, torus_mv_polynomial_compact_observable_inverse,
and Mathlib LipschitzOnWith.extend_real. For the alpha=0 bracket base, use a
TRUE coefficient/finite-cover budget C and tolerance proportional to
delta*maxAbs(zeta)/card(C); torus neighborhood radius must also depend on C
and dimension. Discard/enlarge coordinate-boundary strips explicitly. Keep
the radius FIXED before N and raw inputs so the normalized observable belongs
to the actual compact unit family. This is a continuation plan, NOT a proof.
Use the now PROVED centered/augmented algebra to derive actual Claim 7.7.
Apply complete original reconstruction to case (ii). In case (i), actual
commutator characters still need genuine rational denominator/lattice
integrality proofs: split-basis exponential points are not asserted in Gamma.
Handle true reducible rational nonlinearity filtration/factorization and
degree+nonlinearity induction. Do not treat degree induction alone as enough.

General inverse, small-N completion, corrected multivariate inverse, separate
interval Gowers correlation inverse, rough progressions, cube/Alignment,
and original positive distinct rapidly separated monochromatic FS/FP remain OPEN.

PUBLICATION:
No public repository, PR or prize application yet. The authorized milestone
is full formalization or a genuine unavoidable obstruction; neither reached.

FULL REMAINING SCOPE (retained proof record and latest review):
'''+review['remaining']+'\n'
Path('CURRENT-STATUS.txt').write_text(status,encoding='utf-8')
with Path('CONTINUATION.txt').open('a',encoding='utf-8') as stream:
    stream.write('\n\n2026-10-13 LATEST GOAL ROUND: '+prefix+'\n'+status)
print(json.dumps(s))
