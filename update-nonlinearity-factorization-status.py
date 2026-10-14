from pathlib import Path
import json

prefix='round-native-rational-nonlinearity-factorization'
review=json.loads(Path(prefix+'-review.json').read_text(encoding='utf-8'))
manifest=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert manifest['last_round']['review_file']==prefix+'-review.json'
s=review['verified']
assert not s['full_target_proved']
status=f'''JSP-000168 / Erdos #172 -- 2026-10-13

Goal ACTIVE; StrongConjecture UNPROVED; no unavoidable obstruction found.
Verdict: Partial coverage. Previous goal turn and current round: PROGRESS.
Latest audit: {prefix}
{len(review['new_modules'])} new modules, {s['new_theorems']} new theorems,
{s['new_definitions']} definitions. All final verification awaited terminal success.

NOW PROVED:
'''+ '\n'.join('* '+c for c in review['application_review'][:-1])
status+=f'''

VERIFIED:
{s['project_modules']} own modules, {s['pntplus_modules']} attributed PNT+ modules;
{s['build_jobs']} full-build jobs, {s['selected_axiom_reports']} selected axiom reports.
Every new source passes explicit -DautoImplicit=false with EMPTY logs.
All retained proof-source hashes and selected axiom sets unchanged; only
root/import and axiom registry updated. Standard axioms only. Pinned Lean,
mathlib/PNT+ and all six OpenAI source sections rechecked.
Author checking is NOT independent kernel replay or external peer review.
The exact rational source-slab certificate is re-executed/hash/arithmetic
checked; its numerical issue is repaired for the actual required inverse.

CURRENT EXACT SCOPE:
Actual original Lie commutator annihilation is proved from group pairing zero
by applying the actual group/Lie lower-central equality. Actual relative
lattice integrality implies rational psi values; true rational basis square
gives a canonical rational continuous real extension F on original E.
F restricted to TRUE F_2 equals psi and kills original commutator layer.

TRUE kernel filtration L' has layers Li intersect ker(F) for i>=2 and
original top at zero/one, SAME original D/Gamma/ell. All rational Lie fields
are proved. Actual F_2 dimension and natural nonlinearity sum STRICTLY drop.
Actual highest layer j and rational y with F(y)=1, F killing L(j+1), and
positive q with Exp(y)^q in original Gamma are selected BEFORE all sources.

GENUINE exact source factorization g(x)=Exp(Q_F(x)*y)*gK(x) is PROVED for
ALL real samples. Q_F is actual nonlinear part of F applied to raw p.
Actual native product, aggregate coefficient collection and zero trimming
construct a TRUE weighted source in L', of actual degree ell. Raw source
filteredness is not assumed, and cancellation across list terms is retained.

SAME original Fourier signal now returns full original inverse OR this
actual smaller filtration and exact source factorization, retaining BOTH
higher P/Q tables, actual positive M/offset/dense V and BOTH original-scale
relative/bracket bounds. General degree has ONLY full lower-degree inverse
premise; degree-two version has NO child inverse premise.

NOT YET PROVED:
The explicit removed factor may be UNBOUNDED. It has NOT yet been split
into a quantitatively small error and bounded-period rational factor.
No large child correlation or observable/Haar transport is inferred from
the exact factorization alone. Hence complete same-degree nonlinearity
induction and the full original inverse still require proof.

NEXT:
See FACTORIZATION-CORRELATION-CONTINUATION.txt (concrete PLAN, NOT proof).
Zero pairing makes the actual bracket affine: use actual dense affine circle
inverse to control Q second binomial coefficient at N^-2 and P(1) at N^-1,
then true quadratic remainder lemma and positive multiplier absorption.
Transfer higher coefficients to raw Q_F. Construct actual small/rational
split, bounded rational periods and finite residue representatives.
Select actual short residue progressions and transport genuine observables/
correlation on the appropriate CONJUGATED lattice quotient; right translation
by arbitrary rational representative is not assumed defined on original G/Gamma.
Return original-scale complete raw coefficient tables and prove actual
degree+nonlinearity induction. Full original small-N branches, corrected
multivariate inverse, separate interval Gowers correlation inverse, rough
progressions, cube/Alignment and StrongConjecture remain OPEN. Explicit
delta-power laws are NOT claimed from fixed-data existential constants.

PUBLICATION:
No public repository, PR or prize application yet. User-authorized milestone
is full formalization or a genuine unavoidable obstruction; neither reached.

FULL REMAINING SCOPE:
'''+review['remaining']+'\n'
Path('CURRENT-STATUS.txt').write_text(status,encoding='utf-8')
with Path('CONTINUATION.txt').open('a',encoding='utf-8') as stream:
    stream.write('\n\n2026-10-13 LATEST GOAL ROUND: '+prefix+'\n'+status)
Path('NONLINEARITY-CONTINUATION.txt').write_text(
    'COMPLETED geometry and exact algebraic source-factorization milestone, 2026-10-13.\n'
    'Actual Lie commutator annihilation/rational extension/kernel filtration and\n'
    'strict natural nonlinearity drop are proved. Exact weighted residual source\n'
    'factorization is also proved, with a possibly UNBOUNDED removed factor.\n'
    'Quantitative small/rational split and correlation transport remain OPEN.\n'
    'See CURRENT-STATUS.txt, '+prefix+'-mathematical-review.txt\n'
    'and FACTORIZATION-CORRELATION-CONTINUATION.txt (next PLAN, NOT proof).\n',encoding='utf-8')
print(json.dumps(s))
