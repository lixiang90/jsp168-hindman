from pathlib import Path
import json

summary = json.loads(Path('round-mv-binomial-inverse-checks.json').read_text())
Path('CURRENT-STATUS.txt').write_text(f'''JSP-000168 / Erdos #172 — 2026-10-12

Goal ACTIVE; full original target unproved; no unavoidable obstruction found.

Latest round: 5 modules, 21 theorems, 4 definitions. ACTUAL full multivariable
monomial-to-binomial integer transform and ORIGINAL rough-box basis polynomial
expansion, including exact constant-plus-positive-index form in the paper.
True tensor row budget preserves N^-totalDegree errors with SAME original q/v.
COMPLETE genuine scalar and STANDARD TARGET-TORUS BINOMIAL observable inverses
hold for arbitrary fixed dimensions/degrees and EVERY positive original N.
Actual scalar original large-box binomial small-value inverse includes constant
and eps=0 with SAME q and retained original sufficiently-large-N threshold.
No basis, character, coefficient or inverse existence input at these roots.

Retained complete scalar multiparameter phase/observable/all-coefficient
small-value inverses and genuine target-torus monomial/character inverse,
including actual continuous nonzero lattice-integral real character.
Actual target measure is EXPLICIT normalized Pi(circle Haar).
Fixed-data bounds only; no power-law delta rates claimed.

Full build: {summary['project_modules']:,} own modules, {summary['pntplus_modules']} attributed PNT+ modules,
{summary['build_jobs']:,} successful jobs, {summary['selected_axiom_reports']:,} selected axiom reports.
Only propext, Classical.choice, Quot.sound; all prior registered source
hashes/axiom sets and six pinned OpenAI sections retained. Source scan excludes
sorry/admit/custom axiom/unsafe/native_decide/implemented_by.
Author verification only; independent kernel replay and peer review not claimed.

NEXT native abelian quotient coordinates/normalized Haar/metric-family transfer,
then genuine NONABELIAN orbit-equidistribution quantitative Leibman input and
corrected equal-cube assembly. Rough-step descent/density/dimension/scales,
Alignment and full positive rapidly separated extraction remain open.
SEPARATE unfinished input: HasNativePeriodicIntervalInverse is interval
Gowers-to-nilsequence CORRELATION existence, not orbit-equidistribution;
current standard torus theorem does NOT discharge it. HasAlignmentMonomialRecurrence
also remains an explicit independent unproved existence input.

Public repository, PR and prize application not created/submitted.
Latest audit: round-mv-binomial-inverse-review.json.
Inventory/hashes: verification-manifest.json. Resume: CONTINUATION.txt.
''', encoding='utf-8')
with Path('CONTINUATION.txt').open('a', encoding='utf-8') as stream:
    stream.write('''

Latest audited continuation, 2026-10-12: ACTUAL multivariable binomial
expansion/integer modular transfer and COMPLETE standard torus BINOMIAL inverse.
Five modules; twenty-one theorems, four definitions; twenty-five new reports.
Verified totals: '''+json.dumps(summary)+'''.

MvBinomialCoefficients DEFINES fixed full exponent box mvBinomialBox(kappa,D),
including zero, true NATURAL INTEGER weight W(I,J)=product_j(I_j!*S(J_j,I_j)),
and actual alpha_I(p)=sum_J coeff_J(p)*W(I,J). Every original bounded-total-degree
index lies in the box. True zero weights below any coordinate and true nonzero
weight monotonicity |I|<=|J| are proved; no triangularity assumption.
MvBinomialMonomialExpansion maps the retained PROVED univariate Stirling
polynomial identity through actual Polynomial.eval2RingHom(C)(X_j). True
finite product/sum exchange and actual positive REAL factorial cancellation
give exact ordinary monomial expansion in ORIGINAL roughMvBinomialPolynomial.
No real division on a quotient circle is used.

MvPolynomialBinomialExpansion proves ORIGINAL support belongs to fixed box,
actual monomial box representation and actual polynomial binomial expansion
p=sum_I C(alpha_I)*roughMvBinomialPolynomial(I). All above-total-degree-D alpha
are genuinely zero. Actual alpha(linear character projection)=sum_j k_j*alpha(p_j)
is proved by real original coefficient sums and actual finite sum exchange.
Exact paper form p=C(alpha0)+sum_{0<|I|<=D} C(alpha_I)*originalBinomial(I) is
PROVED by actual zero coefficients, true zero-weight iff zero vector, and actual
binomial basis at zero=1. Original old basis is used throughout; no invented
basis or assumed representation. Zero degree and zero variable dimension covered.

MvBinomialCoefficientModOne proves actual positive natural tensor row budget
mvBinomialCoefficientBudget(kappa,D)=scalarBinomialCoefficientBudget(D)^card(kappa).
Actual row sum=sum_J W(I,J) is product of one-coordinate row sums, each bounded
by the retained PROVED scalar row budget. Actual SAME q*alpha_I is an INTEGER
weighted sum of SAME q*beta_J. Retained true weighted modular bound, true zero
weights and N>=1 preserve N^-|I|. Lower-weight parameter 1 never borrows absent
constant control; parameter 0 permits true all-coefficient small-value bounds.

MvBinomialPolynomialInverse proves THREE GENUINE root inverses without assumed
character/basis/phase/coefficient/multiplier existence:
scalar_mv_binomial_observable_inverse uses complete scalar observable inverse
on SAME p/N/F, retains SAME q and controls EVERY positive alpha_I on EVERY
positive N. scalar_mv_binomial_small_values_inverse uses complete scalar
all-coefficient small-value inverse with ORIGINAL N>=A and zero tolerance;
retains SAME q and original samples, and controls EVERY alpha INCLUDING constant
and eps=0 with enlarged fixed original threshold/error budget. Actual above-degree
zero alpha extend both statements to all multiindices.
torus_mv_binomial_observable_inverse uses complete standard target-torus original
monomial inverse on SAME vector p/N/F, retaining SAME ACTUAL nonzero integer
horizontal vector v and original l1 size. Actual alpha projection identity and
true degree of projection transfer EVERY original positive binomial coefficient
sum_j v_j*alpha_I(p_j), with SAME v and original N^-|I| scale. Fixed enlarged
B=tensorBudget*A+A precedes all coefficients,N,F; no reselected character.
This is the actual BINOMIAL form of corrected equal-cube input for STANDARD
torus, not yet the general native/nonabelian nilmanifold theorem.

Full source/hash/pin/build/axiom audit retained every earlier registered source,
axiom set and pinned OpenAI/Lean/mathlib/PNT+ data. Standard axioms only; author
verification, NOT independent kernel replay or external peer review. Original
StrongConjecture still unproved. Goal ACTIVE, no unavoidable obstruction.
No public repository, PR or prize application yet.

NEXT native abelian quotient/coordinate/normalized-measure transfer, then actual
NONABELIAN quantitative Leibman orbit input. NativeNilmanifoldData.lean supplies
actual finite-dimensional real model E, Lie group G, simply connected/connected
nilpotent group, specified discrete cocompact subgroup Gamma, compatible metric
and actual IsOpenQuotientMap for the metric topology. Its metric is ANY compatible
metric, not explicitly a smooth Riemannian metric. Do NOT assume a native/standard
torus homeomorphism is uniformly Lipschitz merely from topology compatibility.
For native abelian case, use actual global logarithm and true integer lattice
basis to construct actual quotient homeomorphism to standard UnitAddTorus.
Then transfer normalized product Haar explicitly and transfer the ACTUAL compact
unit-native-observable family by continuous/isometric sup-norm pullback. Genuine
finite compact Fourier approximation can handle that pulled-back compact family;
generalize finite-family selection to actual compact observable sets if needed,
rather than assuming an unproved Lip constant. All constants must still precede
polynomial,N,observable. Add actual continuous-linear integer character/operator
norm bridge before using RoughNativeHorizontalCharacterGrid if needed; current
torusIntegerCharacter is an actual continuous additive hom with lattice integrality.

Relevant retained genuine sources: NativeFilteredHorizontalCharacterCoordinates,
RoughNativeHorizontalCharacterGrid, NativeLieLogarithmCharacter, NativeLatticeRationalCharacter,
NativeLieGlobalTopology/Logarithm and actual original fixed coefficient/support,
corrected equal-cube tiling/translation/integer reconstruction. Inspect their
actual quantified hypotheses; do not assume the general orbit hproduce.
RoughNativeComplexBadFamily and RoughNativeZeroDimension already prove actual
zero-dimensional no-bad-family facts; inspect/reuse rather than duplicate them.
General rough-step descent remains to be assembled with true analytic inputs.

SEPARATE unfinished GOWERS inverse: source
NativePeriodicIntervalInverseThreshold.lean defines HasNativePeriodicIntervalInverse(s,d)
as existence of fixed finite list of NativeNilmanifoldData(s), fixed Lip bounds
and gamma>0 BEFORE q,K and unit v:ZMod(q)->R. Large actual interval U^d norm at
length K*q must give actual linear-nilsequence correlation obs(g^n*x). Current
torus orbit-equidistribution inverse does NOT discharge it. Original OpenAI
05_prediction.tex, around lines 472 onward, explicitly cites GTZ finite-list
linear-nilsequence inverse for t>=2, step<=t-1. Cases t=2,3 lower order, higher
orders GTZ Theorem1.3 with correction. Do NOT claim this proposition for arbitrary
incompatible s,d. Actual interval norm is normalized vertex cube mean (zero
extension divided by indicator norm), NOT automatically cyclic Gowers norm:
CyclicIntervalPositiveNormTransfer.lean defines integerIntervalPeriodicGowersValue
as dyadic real root of actual integerIntervalPeriodicCubeMean. It proves one
fixed large K transfer FROM positive cyclic norm TO interval norm, not an automatic
equality for all K. Read actual interval cube normalization before building U2 base.
HasAlignmentMonomialRecurrence remains a distinct independent unfinished input.

Actual nonabelian orbit-equidistribution, separate full interval Gowers inverse,
positive-probability Alignment/conditional face laws, density/dimension/scales/
cofinal rough comparison and final positive rapidly separated FS/FP extraction
remain open. Keep the full original goal intact/ACTIVE; public repo/PR/prize
follows real completion or a real unavoidable obstruction, never intermediate
components masquerading as the full original-prize proof.
''')
