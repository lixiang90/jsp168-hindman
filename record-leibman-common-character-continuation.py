from pathlib import Path
import json

prefix = 'round-leibman-common-character'
c = json.loads(Path(prefix+'-checks.json').read_text())
m = json.loads(Path('verification-manifest.json').read_text())
assert m['last_round']['review_file'] == prefix+'-review.json'
assert c['project_modules'] == 1931 and c['selected_axiom_reports'] == 8061
assert c['new_theorems'] == 7 and c['new_definitions'] == 0
assert c['standard_axioms_only'] and c['retained_proof_sources_unchanged'] and c['retained_axiom_sets_unchanged']
assert not c['full_target_proved'] and not c['independent_kernel_replay']
note = '''

Latest audited continuation, 2026-10-12: one common actual candidate,
direction/origin density and genuine monomial spanning.
5 modules, 7 theorems, no new definitions. Verified totals: {checks}.
Together with round-leibman-dense-directions this continuation has 14 new
modules, 30 theorems, 2 definitions and 32 selected axiom reports.

Actual finite real weight bounds give actual large-entry density. A genuine
finite union and commuted sums prove one common candidate exists, with at
least delta/(2*|A|) of original directions, each with at least that fraction
of original origins. Nonempty A is derived from true output density.
Actual short-line averaging converts this to delta/(8*|A|) direction and
origin fractions for the true length floor(N/L^2) and original equal cube.
Analytic production of a candidate on each large short line is EXPLICIT
UNPROVED INPUT, not a new axiom and not claimed to have been constructed.

Actual nonzero Gamma-integral bounded horizontal functionals enter the SAME
original filtered grid, further filtered by the exact original norm <=M.
Common selection preserves actual nonzeroness/integrality and this norm.
The actual direction-size condition 8*d*|A|<delta*L gives d*L^n<|T|*L.
Genuine Schwartz-Zippel spanning then gives the actual monomial span=top
for those same directions and the same candidate, with many origins each.
Finite n decidable-equality implementations are reconciled by true pointwise
finite-set equality; no source options, hidden assumption or old basis
identification was introduced.

Next prioritize GENUINE analytic existence and small-value inverse inputs,
rather than further conditional restatements of finite selection.
Reviewed primary sources: https://arxiv.org/pdf/1311.6170v3, Section 2
Propositions 2.2/2.3 and Section 3; original Green-Tao
https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf.
Erratum Proposition 2.3 assumes actual polynomial modular values <=eps on
delta*N1*...*Nt actual integer points, eps<delta/10, and derives a bounded
multiplier with ALL smooth coefficients O_delta(eps), including constant.
Its proof uses scalar-torus inverse Proposition 2.2 for multiples lambda*g,
pigeons finitely many q_lambda, then original GT Lemma 3.2 (linear modular
small-value inverse) to improve the error to eps. The printed proof's appeal
to Proposition 2.3 at that intermediate step is self-referential; the preceding
Proposition 2.2 is the intended input. This is a repairable reference typo,
not an unavoidable mathematical obstruction.
Original GT Theorem 2.9 one-parameter nilsequence inverse remains open.
Original GT Lemma 3.2 (Annals p.484, PDF p.20) first obtains q bounded by
delta using the linear torus inverse Proposition 3.1; beta=norm(q*alpha)
is O_delta(1/N). Count interval hits along progressions of step q to get
delta*N <= (1+eps/beta)*(2*q+beta*N). Handle beta=0 explicitly. After
separate small-N and large-eps cases, remaining terms give
beta=O_delta(eps/N). Genuine Fourier approximation plus geometric phase
sum estimates are needed for Proposition 3.1; a conditional count inequality
alone does not prove this analytic input. Prioritize this genuine analytic
base case and actual interval hit count next; inspect existing circle
Fourier/Stone-Weierstrass material before adding redundant infrastructure.
An all-direction bounded product of scalar multipliers may retain original
dense T instead of thinning again, since OpenAI fixes delta and L and needs
only a fixed-data constant independent of N and polynomial coefficients.
No polynomial rate in delta/L is currently asserted. Still prove actual
analytic multipliers and their uniform bound before any such product.

No full StrongConjecture, unavoidable obstruction, public repository, PR or
prize application. Rough descent, Alignment and final extraction remain open.
Original full target remains the only goal and submission target.
'''.format(checks=json.dumps(c, ensure_ascii=False))
with Path('CONTINUATION.txt').open('a', encoding='utf-8') as stream:
    stream.write(note)
Path('CURRENT-STATUS.txt').write_text(f'''JSP-000168 / Erdos #172 — 2026-10-12

Goal ACTIVE; complete original target unproved; no unavoidable obstruction found.

This continuation: 14 new modules, 30 theorems, 2 definitions. Actual dense
monomial spanning; fixed-data bounded integer/modular reconstruction; one
simultaneous multiplier; actual original horizontal grid enlargement.
Then one common candidate/character, exact direction/origin densities and
actual spanning direction sets, conditional on explicit analytic line outputs.

Full build: {c['project_modules']:,} own modules, 9 attributed PNT+ modules,
{c['build_jobs']:,} successful jobs, {c['selected_axiom_reports']:,} selected axiom reports.
Only propext, Classical.choice, Quot.sound; all prior proof source hashes and
axiom sets retained. Registered source scan excludes sorry/admit/custom axiom/
unsafe/native_decide/implemented_by. Author verification only; independent
kernel replay and external peer review not claimed.

Main remaining: genuine one-parameter quantitative character existence,
scalar/multivariate modular small-value inverse and actual polynomial/
difference/binomial compatibility and equal-cube inverse assembly.
Finite common selection and reconstruction are proved; their analytic inputs
are not. Fixed-data bounds are proved; power-law rates in L/delta are not.
Rough-progression descent/density/dimension/scales, Alignment and final
positive rapidly separated monochromatic sums/products extraction remain open.

Public repository, PR and prize application not created/submitted.
Latest audit: {prefix}-review.json; prior round-leibman-dense-directions-review.json.
Inventory/hashes: verification-manifest.json. Resume details: CONTINUATION.txt.
''', encoding='utf-8')
print('Recorded common-character selection continuation.')
