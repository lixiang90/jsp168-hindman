from pathlib import Path
import json

prefix = 'round-native-rational-zero-slope-bracket'
review = json.loads(Path(prefix+'-review.json').read_text(encoding='utf-8'))
manifest = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert manifest['last_round']['review_file'] == prefix+'-review.json'
s = review['verified']
assert s['full_target_proved'] is False
status = f'''JSP-000168 / Erdos #172 -- 2026-10-13

Goal ACTIVE; StrongConjecture UNPROVED; no unavoidable obstruction found.
Verdict: Partial coverage. Full original FS/FP and full Lean completeness
for a prize submission remain OPEN. Previous goal turn classified PROGRESS.
Latest audit: {prefix}
{len(review['new_modules'])} new modules, {s['new_theorems']} theorems,
{s['new_definitions']} definitions. Every final verification awaited terminal success.

NOW PROVED:
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
or external peer review. The old exact rational source-slab certificate was
re-executed, copied/hash recorded and its arithmetic checked; NOT Lean
measure proof of that counterexample.

CURRENT EXACT SCOPE:
The reviewed source slab-volume issue is now repaired by formally proved
signed canonical-circle Haar transport, actual product-Haar Tonelli,
coordinate-boundary loss and corrected full torus neighborhood bounds.
Tolerance factor and radius retain actual fixed cover/coefficient/dimension
budgets BEFORE all beta/zeta/gamma/N. ACTUAL UNIT distance cutoff, dense
discrepancy and original RANGE-N torus linear inverse are proved.

The ZERO-LINEAR-SLOPE fractional bracket inverse is FULLY PROVED for ANY
finite index type: actual REAL coefficient bounds at ORIGINAL N^-1 scale
OR an ACTUALLY NONZERO bounded integer vector with small original dot gamma.
Empty-index and zero-vector cases are included. All budgets precede every
raw unbounded beta/zeta/gamma and every positive N. No bracket oracle,
unsupported power law or fake character nonzeroness is used.

The FIRST Claim 7.7 unrestricted-alpha mixed alternative is PROVED by an
ACTUAL application to augmented coordinates: zeta circle bounds OR an
ACTUAL pair (k,r), not both zero, with small k dot gamma+r*alpha and bounded
size. This is APPLIED to SAME original nonzero Fourier signal, preserving
actual relative character/grid/norm, bounded positive NATURAL M, actual
integer offset and BOTH original higher P/Q monomial/binomial tables.
General degree retains ONLY FULL desired lower-degree child inverse premise.
Degree-two FIRST mixed alternative has NO child inverse premise.

ACTUAL second corrected input is proved: N*abs(nearest-integer residual)<=A,
corrected coefficients <=R*(Z+1), SAME useful-shift circle error <=R*B,
for either sign of r. This does NOT yet prove the full SECOND Claim 7.7
alternative (bounded multiplier making zeta near integers OR nonzero small
k dot gamma). General SMALL-LINEAR-SLOPE bracket inverse remains OPEN.

NEXT:
Detailed concrete continuation plan: SMALL-SLOPE-CONTINUATION.txt (NOT proof).
Prove actual relative affine slope bound using already proved
unit_circle_affine_small_value_inverse / unit_circle_strong_linear_recurrence.
Use genuine fixed-length complete interval blocks L=N/J, control leftover
loss and select one ACTUALLY dense block. Freeze actual alpha on that block.
Extend actual RANGE-N torus/zero-slope inverse to actual affine basepoint,
with exact Fourier basepoint modulus/Haar/unit identities. Transport L^-1
bound back to SAME original N via PROVED N/L<=2*J.

Then APPLY second small-slope inverse to ACTUAL corrected parameters to
prove full Claim 7.7. Apply prior complete original case-(ii) reconstruction.
Case (i) needs actual commutator character rational denominators/lattice
integrality; split-basis exponential points are NOT asserted in Gamma.
Handle true reducible rational nonlinearity filtration/factorization and
degree+nonlinearity induction; degree induction alone is insufficient.

General original inverse, source small-N completion, corrected multivariate
inverse, separate interval Gowers correlation inverse, rough progressions,
cube/Alignment and final original positive distinct rapidly separated
monochromatic FS/FP remain OPEN.

PUBLICATION:
No public repository, PR or prize application yet. Authorized milestone
is full formalization or a genuine unavoidable obstruction; neither reached.

FULL REMAINING SCOPE (retained proof record and latest review):
'''+review['remaining']+'\n'
Path('CURRENT-STATUS.txt').write_text(status,encoding='utf-8')
with Path('CONTINUATION.txt').open('a',encoding='utf-8') as stream:
    stream.write('\n\n2026-10-13 LATEST GOAL ROUND: '+prefix+'\n'+status)
print(json.dumps(s))
