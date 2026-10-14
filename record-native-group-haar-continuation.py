from pathlib import Path
import json

prefix = 'round-native-group-haar'
summary = json.loads(Path(prefix+'-checks.json').read_text())
status = f'''JSP-000168 / Erdos #172 — 2026-10-12

Goal ACTIVE; StrongConjecture unproved; no unavoidable obstruction established.

Latest round: 8 modules, {summary['new_theorems']} theorems, {summary['new_definitions']} definitions.
ACTUAL bi-invariant sigma-finite Haar is CONSTRUCTED on ORIGINAL group G
for EVERY NativeNilmanifoldData(s), including NONABELIAN and step/dimension zero.
It is ORIGINAL exponential pushforward of ACTUAL basis additive Haar, using
ORIGINAL specified lattice filtered real basis and EXPLICIT Borel spaces.
Left/right/conjugation invariance, compact finiteness, open positivity and
sigma-finiteness are GENUINELY proved; no Haar existence/right invariance assumed.

Original Ad(g)-identity is nilpotent from TRUE original lower-central lowering.
Actual det Ad(g)=1. ORIGINAL dexp defect is nilpotent; true det dexp=1 and finite
inverse determinant=1. ORIGINAL global log-left translation is smooth and
has Jacobian one by TRUE manifold chain identity dexp(Tg(v))*fderiv(Tg,v)=dexp(v).
Actual global change of variables, not topology alone, proves volume preservation.

Original group is Polish and locally compact. Original discrete lattice is
countable. ORIGINAL nonnormal coset map is a covering map both canonically
and in SPECIFIED original compatible metric, via genuine topology equality.

Prior COMPLETE native ABELIAN ordinary/binomial cube inverse and corrected
real-box finite obstruction remain retained, with SAME original character,
common fixed bound, arbitrary fixed B/L observables and actual original Haar.
All complete scalar/standard torus analytic/binomial inputs remain retained.

Full build: {summary['project_modules']:,} own modules + {summary['pntplus_modules']} attributed PNT+;
{summary['build_jobs']:,} successful jobs; {summary['selected_axiom_reports']:,} axiom reports.
Standard axioms only (propext, Classical.choice, Quot.sound). All earlier
registered source hashes/axiom sets and six pinned OpenAI sections retained.
AUTHOR verification only; no independent kernel replay or peer review claimed.

NEXT construct ACTUAL relatively-compact measurable fundamental domain for
ORIGINAL countable discrete Gamma.op action, positive finite group-Haar mass,
then normalized invariant probability on ORIGINAL NONNORMAL G/Gamma. Group
Haar is NOT quotient probability. Use actual covering/local injectivity,
local compactness and compact quotient; DO NOT assume fundamental-domain
existence or quotient invariant probability. Then central-fiber Fourier
quantitative Leibman induction, rough-step descent/density/dimension/scales,
Alignment and final positive rapidly separated FS/FP extraction remain open.
Generic Fintype rough-family transport and bad-index residue Haar comparison
also remain to assemble.
SEPARATE HasNativePeriodicIntervalInverse is interval Gowers-to-nilsequence
CORRELATION existence, NOT discharged by group Haar/current orbit results.
HasAlignmentMonomialRecurrence remains a separate explicit unproved input.

No public repository, PR or prize application created/submitted.
Latest audit: {prefix}-review.json; inventory: verification-manifest.json.
Resume: CONTINUATION.txt; full original goal remains ACTIVE.
'''
Path('CURRENT-STATUS.txt').write_text(status, encoding='utf-8')
with Path('CONTINUATION.txt').open('a', encoding='utf-8') as stream:
    stream.write('\n\nLatest audited continuation, 2026-10-12: '+prefix+'\n'+status)
    stream.write('Verified totals: '+json.dumps(summary)+'\n')
    stream.write('''
NilpotentLinearDeterminant proves det(1+f)=1 from actual nilpotent charpoly
X^finrank evaluated at -1. End algebraMap(-1)-f=(-1) smul (1+f) is a TRUE ring
identity. Nonzero (-1)^finrank cancels; no positive-dimension assumption.
NativeLieAdjointUnipotent uses ORIGINAL nativeLieAdjoint_sub_mem_lowerCentral_next
to prove actual (Ad(g)-1)^k maps layer j to j+k, actual nilpotencyClass power
zero, genuine ORIGINAL linear nilpotency and det Ad(g)=1. Original group class
zero supported. At operator applications write ((A-1)^k) v, not (A-1)^k v.

NativeLieDexpDeterminant uses ACTUAL original dexp defect finite formula and
nilpotencyClass power zero to get nilpotency of dexp-id. Actual det dexp=1;
finiteInverse*dexp=identity gives actual finite inverse determinant one.
Actual ContinuousLinearMap.toLinearMapRingHom is the correct ring transport;
change to its explicit application before IsNilpotent.map when coercions stick.

NativeLogLeftTranslation CONSTRUCTS original Tg=log compose Left_g compose exp
as global Homeomorph E E; true smoothness from actual C-infinity maps. At original
v set u=Tg(v). Relative maps P(y)=exp(u)^-1*exp(y), R(y)=exp(v)^-1*exp(y) satisfy
ACTUAL GLOBAL P compose Tg=R. Actual manifold chain rule and ORIGINAL dexp
definition give dexp(u) compose fderiv(Tg,v)=dexp(v). TRUE determinant product
and det dexp=1 yield pointwise original log-left Jacobian=1. IsTopologicalGroup G
is an ORIGINAL native data field; the homeomorphic multiplication needs it.

SmoothUnitJacobianMeasure uses ACTUAL Mathlib full-space Jacobian change of
variables, actual HasFDerivAt and actual injectivity/surjectivity; determinant-one
density is truly constant one. Use withDensity_const plus one_smul: withDensity_one
does not simplify the literal fun x=>1 density here. No volume-invariance hypothesis.
NativeLieLogCoordinateHaar is EXPLICIT exp map basis.addHaar on ORIGINAL G with
EXPLICIT model/group Borel measurable structures. BorelSpace E must be explicit
both in proof and in statements mentioning basis.addHaar (letI := <rfl>).
TRUE exponential/Tg commutation plus exact measurable map_map prove left invariance.
TRUE exponential/Ad conjugation identity plus ACTUAL det Ad=1 give conjugation
invariance. ORIGINAL right translation equals Left_g compose Conj_(g^-1), so true
map_map gives right invariance. Explicit typed Measurable(fun x=>g*x) avoids reverse
rewrite mismatch with coercion of Homeomorph.mulLeft g. Actual Haar class is built
from compact finiteness/open positivity under original homeomorphism and PROVED
left invariance. Sigma-finite map uses genuine measurable embedding and basis
Haar sigma-finiteness. No assumed group measure or unimodularity existence.

NativeNilmanifoldGroupHaar specializes actual construction to EVERY ORIGINAL
NativeNilmanifoldData(s), with original fixed Gamma filtered real basis. ACTUAL
IsHaarMeasure/IsMulRightInvariant/SigmaFinite proofs are supplied for that actual
measure. Generic original lattice need NOT be normal; no abelian restriction.
NativeNilmanifoldQuotientCovering proves original G Polish/local compactness,
original Gamma countability, actual canonical quotient covering and covering
in the original D.metric topology. These are ACTUAL next construction inputs.

NEXT concrete fundamental-domain route (not yet implemented/proved):
Mathlib Topology/Covering/Quotient.lean Subgroup.isQuotientCoveringMap accepts
ACTUAL IsDiscrete Gamma, with NO normality. .isCoveringMap.isLocalHomeomorph
.isLocallyInjective supplies actual open injective patches. LocallyCompact
exists_compact_subset shrinks each patch to precompact open neighborhood.
Actual compact G/Gamma + open quotient map give a FINITE subcover of images.
Index finite patches by Fin m; disjointize U_i by subtracting pi^-1 of earlier
images pi(U_j), j<i. The finite union F is measurable, relatively compact,
surjects onto ORIGINAL cosets and pi is injective on F. Then ORIGINAL Gamma.op
action has exactly one representative in F; IsFundamentalDomain.mk' applies.
Countability of original Gamma and true nonzero Haar show mass(F)>0 (otherwise
countable translates would make all G null); relative compactness gives finite
mass. Restrict actual group Haar to F and map original pi, then normalize by
that ACTUAL positive finite mass. Mathlib MeasureTheory/Measure/Haar/Quotient.lean
and fundamental-domain measure equality give actual original G-invariance.

Useful exact library sources: MeasureTheory/Constructions/Polish/Basic.lean
Quotient.borelSpace (around 627) and EXACT CosetSpace.borelSpace instance (around 642)
handle quotient measurable structure for Polish original G and second-countable
T2 NONNORMAL cosets. CosetSpace.borelSpace may need an explicit letI because
typeclass inference for MeasurableSMul G (G/Gamma) has a documented gap.
Canonical coset T2 follows from discreteLattice_isClosed plus proper coset
action, or by transporting D.metric T2 through nativeNilmanifold_metric_topology.
Original G second countability follows from proved Polish/homeomorphism; actual
open quotient map transports second countability to ORIGINAL cosets. Countable original Gamma is already proved. Covering basic gives
IsCoveringMap.isLocalHomeomorph (around 339). IsLocalHomeomorph.isLocallyInjective
(around 222) gives open neighborhoods with genuine pi injectivity.
Topology/Compactness/LocallyCompact.lean exists_compact_subset (around 148).
IsCompact.elim_finite_subcover (Compact.lean around 198) gives actual finite cover.
MeasureTheory/Group/FundamentalDomain.lean IsFundamentalDomain.mk' (around 86),
quotientMeasureEqMeasurePreimage_quotientMeasure (around 794) then actual
QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient in Haar/Quotient.
DO NOT turn F, quotient invariant probability or future Fourier theorem into
an assumed existence input. Group Haar is now genuine, quotient probability
still unfinished. Central-fiber Fourier/quantitative Leibman/nonabelian orbit
inverse, separate interval Gowers inverse, Alignment and full target remain OPEN.

All earlier sources/axiom sets/pins retained, author verification only. Public
repo/PR/award unfinished; original goal ACTIVE without an unavoidable blocker.
Next audit OLD=round-native-group-haar. Preserve 2 inherited unregistered
circle-bump drafts byte-for-byte in work-in-progress.
''')
print(json.dumps(summary))
