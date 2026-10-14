from pathlib import Path
import json
import re

prefix = 'round-native-rational-dense-relative-character'
old = 'round-native-rational-nonzero-relative-character'
base = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained = {f['path'] for f in base['files']}
modules = sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules) == 9, modules
components = [
    'ACTUAL arbitrary bounded complex sequences have a positive-density set of genuine positive derivative shifts. Each derivative mean uses its TRUE remaining interval N-h, with 0<h<N and N-h >= (delta^2/8)*N. Exact natural-range/integer-Ico mean transport is proved. No truncated or zero-extended sample is identified with a full original sample.',
    'Actual native rational-terminal Fourier projection is globally bounded by ONE on original unit observations. Its genuine large original univariate orbit mean produces a positive-density set of actual original Fourier derivative means on SAME actual remaining intervals, with no unit-Lipschitz assumption on the projected observable.',
    'A general finite witness-selection theorem proves ONE ACTUAL common witness on a nonempty subset, preserving an explicit cardinality bound involving the FIXED witness-list cardinality. Source-dependent witness choices do not redefine the finite list.',
    'TRUE retained sample lengths transfer monomial and paper-binomial coefficient bounds to the ORIGINAL N scale. The proved inflation A*tau^(-ell) precedes all source coefficients and shifts. The finite nonconstant degree range 1<=j<=ell is explicit; no vanishing theorem outside this range is claimed.',
    'GENUINE common ACTUAL nonzero relative horizontal character is extracted on a positive-density subset of useful shifts CONDITIONALLY on the FULL desired lower-degree inverse. The finite CONTINUOUS-character list, positive density, norm bound and BOTH ORIGINAL-scale coefficient budgets precede ALL original polynomials with unbounded coefficients, ALL observations and sample lengths. Actual remaining lengths and integer shifts agree literally with the genuine child-inverse inputs.',
    'Degree-TWO common ACTUAL nonzero RELATIVE character on a positive-density shift set is FULLY PROVED with NO child inverse premise, using the genuine degree-one inverse on TRUE child geometry/filtration. This is univariate and does NOT close the degree-two original nonzero inverse branch.',
    'When the ACTUAL difference character is ZERO, the complete actual relative scalar polynomial equals the original compact-normalized diagonal scalar. ACTUAL relative nonzeroness then proves original diagonal nonzeroness. TRUE lattice/basepoint/linear normalizations preserve all NONCONSTANT ORIGINAL monomial coefficients modulo integers; hence original raw monomial bounds are derived in the explicit 1<=j<=ell range. The general nonzero difference/cancellation cases, parent binomial reconstruction and full original inverse remain OPEN.',
    'Genuine normalized complex Cauchy-Schwarz/energy and exact pair-duplication means are checked. These author checks do not constitute independent kernel replay, external review, full formalization or prize eligibility.'
]
remaining = base['last_round']['remaining']
remaining = re.sub(r'NEXT: useful shift selection,[^;]*;',
    'NEXT: actual scalar difference/commutator formula, combined coefficient separation and ORIGINAL nonzero horizontal reconstruction with genuine degree and nonlinearity induction;', remaining)
remaining += '\nNEW DENSE-SHIFT MILESTONE: Actual useful shifts and repeated common relative characters with BOTH ORIGINAL-scale coefficient bounds are now PROVED, conditional only on genuine lower-degree inverse; degree-two version has NO child premise. Pure diagonal (actual difference ZERO) reconstruction of raw original monomial bounds is PROVED in the explicit 1<=j<=ell range. NEXT: original actual nonzero-difference polynomial formula P(n)+Q(n+h)-Q(n)+sigma(h)*n, true group commutator character identities, dense polynomial separation (Green-Tao Lemma 7.6), bracket-polynomial alternative (Claim 7.7), and actual original character reconstruction or refinement of the nonlinearity filtration. Degree induction alone is insufficient for the reducible case: the actual secondary nonlinearity/dimension induction remains required. General original inverse, corrected multivariate inverse, interval Gowers correlation inverse, rough progressions, Alignment and StrongConjecture remain UNPROVED. No unavoidable obstruction has been established. No public repository, PR or prize application yet.'
text = Path(old+'-audit.py').read_text(encoding='utf-8')
for name, value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
    text = re.sub('^'+name+r' = .*$', lambda m: name+' = '+repr(value), text, flags=re.M)
text = text.replace('Audit ACTUAL nonzero child/relative inverse extraction, closed degree-two relative extraction, genuine original diagonal/F_2 character alternatives and complete scalar/coefficient splitting.', 'Audit actual dense useful Fourier derivative shifts, common relative character selection, BOTH original-scale coefficient bounds, complete degree-two dense extraction and raw pure-diagonal monomial reconstruction.')
text = re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions and Green-Tao section 7 equation 7.10: genuine dense useful shifts, repeated relative characters and original-scale bounds; pure-diagonal raw monomial transfer; nonlinear reconstruction and full target open'", text)
Path(prefix+'-audit.py').write_text(text,encoding='utf-8')
review = '''JSP-000168 / Erdos #172: dense actual useful shifts and common relative character
Author mathematical review, 2026-10-13. NOT independent kernel replay or peer review.
Verdict: Partial coverage. StrongConjecture is UNPROVED.

Route: retained OpenAI six-section proof at
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026,
06_rough_progressions, quantitative Leibman input.
Primary auxiliary route:
https://arxiv.org/html/0709.3562v4 (section 7, equation 7.10 and Lemmas 7.5-7.6)
Corrected multiparameter scope: https://arxiv.org/html/1311.6170v3 .

ORIGINAL TARGET: every finite coloring of positive integers has arbitrarily
large distinct positive finite-sums/finite-products monochromatic witnesses.
StrongStatement.lean defines the stronger rapidly separated target only as
a proposition and proves its implication to the original target conditionally.
This round does NOT supply StrongConjecture.

1. Actual dense derivatives
The previously checked positive-lag energy/density results apply to ANY bounded
complex sequence, with the actual large-N condition 4<=delta^2*N. The new generic
wrapper retains the original truncated derivative sum and divides by N-h,
proving N-h>=tau*N where tau=delta^2/8. It preserves 0<h<N, so no zero shift or
empty derivative interval is used. Range-to-Ico transport is an explicit
injective image identity valid even for empty intervals. In the native
application, the original Fourier projection has supremum norm <=1 by the true
projection contraction and original unit pointwise bound. Projected functions
need not be unit Lipschitz; no such input is assumed.

2. Common actual relative character
Apply the PREVIOUS actual nonzero relative inverse to the original p, weighted
degree proof hp, integer h and sample length N-h. It yields an actual nonzero
relative continuous linear functional with both raw monomial/binomial bounds.
Its sole inverse premise is the FULL desired inverse on the ACTUAL lower-degree
relative-then-terminal child. All other inputs are proved. The SAME finite
horizontal grid uses a norm budget A chosen before ALL p, hp, F and N. Converting
the finite linear grid to continuous linear maps is justified by genuine finite
dimensionality; extensional equality proves that the produced functional belongs
to the fixed image list. There is no arbitrary finite-list containment premise.

The generic selection lemma partitions actual useful shifts by one witness from
the fixed finite list. The sum of fiber cardinalities is exactly the original
cardinality. A maximizing fiber gives card(T)<=card(C)*card(U), with U nonempty.
The positive density rho=tau/(card(C)+1) is fixed before the source data and is
positive even if the list is empty; in that case the large-signal antecedent is
impossible because actual extraction would supply a list member. The proof does
not assume the list nonempty for arbitrary geometry in advance.

3. Actual ORIGINAL-scale coefficient bounds
Given tau*N<=M=N-h, for a coefficient of degree j<=ell,
N^j*x <= tau^(-j)*(M^j*x) <= A*tau^(-ell), using 0<tau<=1.
This is proved for ANY nonnegative x, then used for actual circle norms of BOTH
tables. The new coefficient-bound proposition contains exactly degrees
1<=j<=ell; it is an explicit scope restriction, not a claimed universal bound.
The original relative inverse had bounds for all nonconstant indices. The new
round does not prove that out-of-range coefficients vanish. The true scalar
weighted degree is retained, so such a later bridge remains meaningful.

4. Degree-two actual application
The true relative-then-terminal child has bound ell-1=1. The existing full
degree-one inverse discharges the child premise literally, on its own native
model/lattice/metric/filtration. The theorem produces a dense shift set and ONE
actual nonzero RELATIVE character, not an original nonzero horizontal character.
It is univariate; corrected multiparameter induction is still required.

5. Pure diagonal original reconstruction
Assume the ACTUAL F_2 difference component of the selected character is ZERO.
The complete scalar splitting then reduces to the normalized original diagonal
scalar; relative nonzeroness forces its diagonal component nonzero. Earlier
proved original horizontality and lattice integrality apply to this component.
The actual basepoint/linear-step corrections change every nonconstant monomial
coefficient by an integer. Integer equality in the UnitAddCircle is proved
explicitly. Hence original RAW, UNBOUNDED coefficients inherit the relative
monomial bound. No basepoint value, coefficient cap, new character extension or
small-summand inference is assumed. Parent binomial bounds in this subcase are
not claimed by this round. If difference is nonzero, the combined small scalar
does not control the individual scalars and these lemmas cannot be applied.

6. Auxiliary energy module
The unregistered FiniteComplexMeanEnergy module present at continuation start
had elaboration failures. Its star/mean compatibility, pair-duplication rewrite,
positive-cardinality cancellation and multiplication order were repaired and
checked. None of the registered old proof source files were edited. Normalized
Cauchy-Schwarz requires a nonempty source set, and no phase agreement is assumed.

7. Remaining reconstruction obligations and secondary induction
The auxiliary paper proceeds from a common relative character to scalar
separation and a bracket alternative. Its reducible-filtration case requires
a secondary nonlinearity induction. Our dense-shift theorem supplies the
actual common-character stage but not these later stages. A nonzero character
on F_2 killing [G,F_2] need not extend to a horizontal character of G; no such
extension is inferred. The next actual work is the original scalar formula
P(n)+Q(n+h)-Q(n)+sigma(h)*n, true mixed commutator group-character identities,
dense polynomial coefficient separation, bracket reconstruction and the actual
smaller rational filtration in the reducible case. This is further proof work,
NOT an unavoidable mathematical obstruction.

Trust: ordinary classical Lean foundations only, subject to the final actual
axiom logs. Author build/source/hash/axiom checks are not kernel replay by an
independent implementation or external expert verification. The audit records
the pinned Lean/mathlib/PNT+ versions, unchanged previous proof hashes/axioms,
complete build, explicit new-module checks, and retained six pinned OpenAI
section hashes. No full formalization, award eligibility or public priority
claim follows from these partial results.

Answers: addresses original scope CONDITIONALLY as intermediate proof work;
the exact saved project version is checked by attached build/axiom evidence;
does NOT fully solve the original problem; does NOT meet full Lean completeness
for a prize submission. Full target unproved, no unavoidable obstruction,
goal ACTIVE. Publication/application milestone not reached.
'''
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
print(json.dumps(modules))
