from pathlib import Path
import json

prefix = 'round-native-quotient-probability'
summary = json.loads(Path(prefix+'-checks.json').read_text())
status = f'''JSP-000168 / Erdos #172 — 2026-10-12

Goal ACTIVE; StrongConjecture unproved; no unavoidable obstruction found.

Latest round: 9 modules, {summary['new_theorems']} theorems, {summary['new_definitions']} definitions.
ACTUAL normalized invariant probability on ORIGINAL NONNORMAL G/Gamma
constructed for EVERY NativeNilmanifoldData(s), including NONABELIAN.
Actual locally injective precompact finite patch cover is constructed; earlier
patch removal gives MEASURABLE UNIQUE coset representatives. Actual relatively
compact fundamental domain for ORIGINAL Gamma.op is constructed, with POSITIVE
FINITE ORIGINAL group Haar mass. Restrict original Haar to this actual domain,
map ORIGINAL pi, and normalize by ACTUAL mass. Probability and G-action
invariance, translate pushforward and domain-choice independence are proved.

Canonical quotient Borel structure agrees with ORIGINAL specified compatible
metric Borel structure; actual metric quotient compactness, continuous complex
observable integrability, integral bound and translated integral identity proved.
Actual general native quotient probability has EXACT standard Pi(circle Haar)
coordinates in the ABELIAN case by true original action/surjectivity and
probability Haar uniqueness. No measure agreement or homeomorphism Lipschitz
bound assumed.

ACTUAL original RoughNativeComplexBadIndex gives Haar discrepancy on either
ORIGINAL residue sample or ORIGINAL full-box sample, with SAME Q,time,observable,
endpoints/residue,bounds and BOTH original positive cardinalities retained.
Actual uniform finite-mass means equal exact finite set means. This is a genuine
connection to the original bad-index API; affine residue obstruction/scales
production is still to be completed.

Prior actual ORIGINAL group bi-invariant Haar and ALL complete scalar/standard
torus/native ABELIAN monomial/binomial/real-box results remain retained.

Full build: {summary['project_modules']:,} own + {summary['pntplus_modules']} attributed PNT+ modules;
{summary['build_jobs']:,} successful jobs, {summary['selected_axiom_reports']:,} axiom reports.
Only propext, Classical.choice, Quot.sound; old registered source hashes/axiom
sets and all six fixed OpenAI sections retained. AUTHOR verification only,
not independent kernel replay or external peer review.

NEXT use exact canonical abelian probability integral identity to assemble
canonical-measure native abelian inverse/real-box roots. Then connect actual
bad-index residue/full Haar dichotomy to affine t*v+b sampling and scales Z/t;
complete generic finite-index transport and finite obstruction density/descent.
Develop NONABELIAN central-fiber Fourier quantitative Leibman induction using
the NOW GENUINE original quotient probability. Central measure compatibility/
disintegration and general homogeneous invariant probability uniqueness remain
actual work, not supplied assumptions. Full rough-step/density/dimension/scales,
Alignment, separate interval Gowers-to-nilsequence CORRELATION inverse,
HasAlignmentMonomialRecurrence and final positive separated FS/FP remain OPEN.

No public repository, PR or prize application created/submitted.
Latest audit: {prefix}-review.json; inventory: verification-manifest.json.
Resume: CONTINUATION.txt; original full goal stays ACTIVE.
'''
Path('CURRENT-STATUS.txt').write_text(status, encoding='utf-8')
with Path('CONTINUATION.txt').open('a', encoding='utf-8') as stream:
    stream.write('\n\nLatest audited continuation, 2026-10-12: '+prefix+'\n'+status)
    stream.write('Verified totals: '+json.dumps(summary)+'\n')
    stream.write('''
CompactQuotientFinitePatches constructs actual finite precompact injective patch
cover from true open surjective locally injective original quotient map, actual
locally compact group and actual compact cosets. Each local open patch shrinks
to compact K with original point in interior K; actual compact image cover has
finite subcover, indexed by Fin m using actual Fintype.equivFin of finite set.
FinitePatchTransversal DEFINES stratum U_i minus pi^-1 of earlier image patches,
and finite union F. Actual Borel measurability, compact-bound inclusion, true
global pi injectivity and coverage by ACTUAL minimum of nonempty finite patch
set are proved. No finite-cover/transversal existence assumption at native root.

DiscreteCocompactFundamentalDomain proves ORIGINAL Gamma.op RIGHT action has
UNIQUE translate of every x in F: x^-1*y in Gamma gives actual a=op(x^-1*y),
a*x=y. Pi injectivity on F and right action cancellation give uniqueness.
Explicit type ((b • x : G) : G/Gamma) is necessary; otherwise expected coset
type tries to make Gamma.op act directly on cosets. Subgroup.mem_op.mp b.property
gives true original Gamma membership; proof is not definitional by simplifier.
For the unique-existence predicate initial membership, change explicitly to
x*(x^-1*y) in F; rw at beta-reduced predicate failed to find a*x otherwise.
Actual IsFundamentalDomain.mk' applies to actual measurable F and unique right
action representatives. Actual Haar nonzero and countability give positive mass
by IsFundamentalDomain.measure_ne_zero; actual compact containment gives finite
mass. NativeNilmanifoldFundamentalDomain selects ACTUAL original domain and its
spec RETAINS measurable, fundamental, positive, finite AND compact containment.
It uses genuinely proved original group Haar, local compactness and countable
original Gamma for EVERY original native step s. No new existence interface.

FundamentalCosetProbability DEFINES actual map(pi,nu restricted F) and scalar
normalization by (nu F)^-1. True total mass=nu(F), probability, original G-action
invariance and FUNDAMENTAL-DOMAIN independence proved using actual native
fundamental domain equality and IsMulLeft/RightInvariant group Haar. Native
probability root provides all these actual inputs; Gamma never assumed normal.
Use typed hpi : Measurable((up):G->G/Gamma) := QuotientGroup.measurable_coe;
untyped measurable_quotient_mk' rewrites fail and may seek a Setoid instance.
IsFundamentalDomain.quotientMeasure_eq needs explicit measure argument:
hF.quotientMeasure_eq nu hF', not hF.quotientMeasure_eq hF'.

NativeNilmanifoldQuotientProbability CONSTRUCTS actual native normalized quotient
probability from ORIGINAL nativeGroupHaar and ACTUAL nativeFundamentalDomain.
Actual probability and G-action invariant proofs, actual canonical coset Borel,
original compatible metric Borel, original metric compactness and true translate
map equality are proved. Def/proof bodies need explicit letI group/model Borel
measurable spaces even when result type starts with those letI binders.
Canonical quotient sigma-algebra is ACTUAL quotient of original group Borel,
and new native_nilmanifold_metric_coset_borel proves it IS original metric Borel.
Use that BorelSpace instance for integrations of original metric C-functions;
do not need to replace the sigma-algebra by another explicit borel instance.

NativeNilmanifoldProbabilityTesting proves ACTUAL original-metric continuous
complex observables integrable under constructed probability, true integral sup
bound and ORIGINAL action translated integral equality. Its finite-pair Haar
discrepancy split is actual triangle inequality on SAME original means. Use
norm_sub_le for TWO arguments; for A-B via C, rewrite as (A-C)-(B-C), then apply
norm_sub_le. Norm-integral bound uses Measure.real, measure_univ and mul_one.
Use modern `push Not at h`; `push_neg` is deprecated and strict audit rejects warnings.

NativeAbelianCanonicalProbability proves EXACT coordinate pushforward of the
GENERAL native quotient probability through original D.metric torus homeomorphism
equals EXPLICIT Pi(circle Haar). Actual original projection surjectivity and
true original action equivariance provide every torus translation. Actual
native translation map invariance plus true measurable map_map give coordinate
additive invariance. ACTUAL probability and compact whole-group Haar criterion
give IsAddHaarMeasure; actual probability Haar uniqueness yields exact Pi Haar.
True measurable embedding integral_map gives canonical native observable Haar
integral identity. No assumed equality with old separately defined abelian
measure and no unproved Lipschitz bound. Important next bridge: old abelian
native Haar def uses EXPLICIT borel(metric) sigma-algebra, new canonical quotient
uses actual quotient sigma-algebra. They are PROVED equal, not definitionally
equal. Prefer direct new coordinate integral identity to assemble canonical-
measure native abelian roots, with same existing actual compact-family Fourier
and original character polynomial machinery; do not fake a rewrite across
different measure types. Existing root files are hash-retained.

RoughNativeBadIndexHaarComparison proves ACTUAL original complex bad-index pair
produces strict eta/2 Haar discrepancy on original residue sample OR original
full box, with SAME original Q/time, F promoted by true original Lipschitz
continuity, ALL original box/residue/bound data and BOTH original positive
sample cardinalities. Actual FiniteMass.complexExpectation_uniformFinset gives
EXACT original finiteComplexSetMean. This genuine theorem holds for arbitrary
finite input type kappa and every native step s. Next canonical-measure abelian
cube/real-box assembly, residue affine t*v+b and scale Z/t obstruction production,
finite character selection/density/descent and NONABELIAN central Fourier input.

No general homogeneous invariant probability uniqueness across arbitrary group
Haar choices, central disintegration or nonabelian quantitative Leibman claimed.
Full StrongConjecture and separate interval Gowers correlation inverse/Alignment
remain unproved. No unavoidable blocker; goal ACTIVE. Author checking only,
no independent kernel replay/peer review or public repo/PR/prize submission.
Next audit OLD=round-native-quotient-probability; preserve ALL earlier sources,
axiom sets/pins and inherited unregistered circle-bump drafts byte-for-byte.
''')
print(json.dumps(summary))
