from pathlib import Path
import json
import re

prefix = 'round-native-rational-paper-scalar-separation'
old = 'round-native-rational-dense-nonlinear-separation'
base = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained = {f['path'] for f in base['files']}
modules = sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules) == 10, modules
components = [
    'EXACT actual Taylor tails identify every combined coefficient above degree one as P_i plus a TRUE higher Q tail, and identify the linear combined coefficient as P_1+2*Q_2*h+sigma plus the TRUE higher linear Q tail. No separation of unbounded small summands is assumed.',
    'Genuine integer Taylor weights for NATURAL actual shifts h<=N are bounded at the SAME ORIGINAL N^-i scale. A fixed finite Taylor-row budget bounds all actual tails from the PREVIOUSLY PROVED Q higher coefficient bounds. There is no replacement of h by a new scale or assumption that arbitrary real multiplication preserves the circle norm.',
    'ACTUAL higher original diagonal P monomial coefficients (i>=2) are PROVED small by subtracting the already bounded Q tail from actual combined coefficients. The SAME common natural M is used. The original P paper-binomial table also inherits the bounds by true integer triangular weights, without a constant or linear P bound.',
    'TRUE original beta=P(1) is recovered from P_1 using actual degree and P(0)=0. The higher P sum is bounded at ORIGINAL N^-1 scale by its proved N^-i bounds. TRUE paper alpha=second BINOMIAL coefficient of Q is recovered from 2*Q_2 by removing the actual quadratic monomial and controlling ONLY higher Q terms. No Q_2 bound is assumed.',
    'COMPLETE genuine scalar relation beta+alpha*h+sigma on SAME useful shifts is PROVED with SAME natural M and original N^-1 scale. The actual ordinary-linear residual, higher P value-one error and quadratic-binomial correction are all discharged by true integer norm estimates. Both higher P/Q monomial/binomial tables and actual combined coefficients are preserved.',
    'ACTUAL compact original diagonal scalar P has true degree<=ell, P(0)=0 and P(1) EXACTLY equal to the genuine original diagonal real character on SAME normalized group P(1). EVERY original nonconstant relative coefficient bound transports to the true univariate combined polynomial, not only its second coefficient.',
    'The COMPLETE paper scalar separation is APPLIED to SAME ACTUAL native compact P/Q/sigma and common relative character. ALL character-grid/operator/coefficient/density/multiplier/large-N constants precede ALL raw unbounded original source coefficients/observations/sample lengths. The sole inverse premise is the FULL actual lower-degree child inverse. Original nonzero character reconstruction/bracket alternative are NOT claimed.',
    'Degree-TWO COMPLETE actual dense paper scalar separation is FULLY PROVED with NO child inverse premise by the true degree-one inverse on actual child geometry. Its beta/alpha/sigma relation and higher diagonal quadratic bound are substantive, despite the empty Q higher-index range. This is UNIVARIATE and not the full degree-two original inverse.'
]
remaining = base['last_round']['remaining']
remaining += '\nLATEST COMPLETE PAPER SCALAR MILESTONE: Actual higher P (i>=2) and Q (j>=3) monomial/BOTH paper-binomial tables and SAME useful-shift beta=P(1), alpha=second BINOMIAL Q coefficient, beta+alpha*h+sigma modulo-one bound at SAME original N scale are PROVED with ONE bounded common natural M. This COMPLETE scalar stage is APPLIED to SAME native compact original P/Q/sigma/common relative character. Degree-two version has NO child inverse premise. NEXT: actual bracket-polynomial alternative (Claim 7.7), true original commutator character coordinates/operator/integrality/nonzeroness, original horizontal reconstruction OR actual smaller rational nonlinearity filtration/factorization, then genuine degree+nonlinearity induction. Selected representatives come from an ARBITRARY fixed compact coset set, not a canonical fractional-coordinate section: derive actual horizontal/lattice coordinate relation and a FIXED finite bounded integer-offset refinement before using a fractional-part bracket polynomial; do not silently replace the actual selected samples. General native original inverse, small-N completion, corrected multivariate inverse, separate interval Gowers correlation inverse, rough progressions, Alignment and StrongConjecture remain UNPROVED. No unavoidable obstruction found; publication/application milestone not reached.'
text = Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
    text = re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),text,flags=re.M)
text = text.replace('Audit actual dense second-coefficient separation, one bounded common higher multiplier for BOTH nonlinear tables, exact Unit/univariate transport and SAME native compact common-character application.',
    'Audit COMPLETE actual paper scalar separation: original-scale Taylor tails, BOTH higher P/Q tables, exact beta/alpha residual, SAME native application and degree-two child-premise discharge.')
text = re.sub(r"reference_scope='[^']*'", "reference_scope='OpenAI 06_rough_progressions quantitative Leibman route; Green-Tao section 7 Lemma 7.6 COMPLETE scalar stage on SAME actual native P/Q/sigma; bracket alternative/nonlinearity induction/full target open'",text)
Path(prefix+'-audit.py').write_text(text,encoding='utf-8')
review = '''JSP-000168 / Erdos #172: COMPLETE actual paper scalar separation
Author mathematical review, 2026-10-13. Verdict: Partial coverage.
NOT independent kernel replay or external peer review.

Original problem: every finite coloring of positive integers has arbitrarily
large positive distinct monochromatic finite-sums/finite-products witnesses.
StrongConjecture remains UNPROVED. This round finishes the scalar-separation
stage of the univariate quantitative Leibman route, not its full inverse.
Pinned original six-section OpenAI source:
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026,
06_rough_progressions. Auxiliary primary route:
https://arxiv.org/html/0709.3562v4 , section 7, Lemma 7.6 and following Claim 7.7;
corrected multivariate scope: https://arxiv.org/html/1311.6170v3 .

1. Actual algebraic tails
For R_h=P+Q(X+h)-Q+sigma*X, all coefficients i>=2 equal P_i plus the actual
Taylor tail sum over j>i. Terms j<i vanish by integer binomial coefficients,
and j=i cancels the original Q_i. The linear coefficient equals
P_1+2*Q_2*h+sigma plus the actual sum over j>=3 of Q_j*j*h^(j-1).
All finite-set erase/filter identities and exact polynomial coefficient
identities are proved. No merely approximate scalar formula is supplied.

2. Actual circle norms at the original scale
For NATURAL h<=N, each Taylor weight choose(j,i)*h^(j-i) is an INTEGER.
The checked integer-weighted circle-norm theorem bounds the tail by a sum
of weight times norm(M*Q_j). N^i*h^(j-i)<=N^j is proved, and true higher Q
bounds control the result. A finite double-sum Taylor budget depends only
on D, preceding all raw coefficients and h/N. The same argument covers the
linear tail at i=1. Arbitrary real multiplication is NOT asserted to obey
this circle-norm bound; integer shifts from actual useful U are retained.

3. Actual higher diagonal P recovery
For i>=2, M*P_i=M*(R_h)_i-M*TaylorTail_i. Natural multiplier circle bounds
control the first term by M*A, and the PROVED tail bound controls the second.
The triangle inequality now gives a genuine separated P_i bound. It is
not inferred solely from a small combined coefficient. One actual useful
h exists because U is nonempty; the resulting P_i bound holds for every
i>=2 simultaneously with SAME original M and original N^-i scales.

With M<=S and A>=0, fixed C_P=S*A+TaylorBudget(D)*B bounds all these terms,
independent of source P/Q and sample length. Integer triangular Stirling
weights transfer to P's paper-binomial coefficients with lower index 2.
No absent constant/linear bound is imported. Previous higher Q bounds in
BOTH tables are retained with the same common M.

4. TRUE beta=P(1)
Actual polynomial degree and P(0)=0 prove P(1)-P_1=sum_{j>=2} P_j. Integer
weights and N<=N^j for N>=1 give the original N^-1 value-one error from
the already proved higher P bounds. This replaces ordinary P_1 by actual
P(1), not by an assumed equality of these distinct quantities.

5. TRUE quadratic paper alpha
The scalar binomial table is linear in the polynomial, and its quadratic
monomial value is exactly 2*Q_2. Therefore the second binomial coefficient
of Q minus 2*Q_2 is the second table entry of Q with its actual quadratic
monomial removed. That polynomial has zero quadratic monomial coefficient;
its higher coefficients are the SAME original higher Q coefficients.
The actual binomial norm theorem with lower index 2 now proves
N^2*norm(M*(alpha-2*Q_2))<=BinomialBudget(D)*B. No bound on Q_2 itself is
assumed. Multiplication by NATURAL h<=N transfers this correction to N^-1.

6. Complete actual linear relation
The real expression M*(P(1)+alpha*h+sigma) decomposes EXACTLY into the
proved ordinary-linear residual, value-one correction and the quadratic
binomial correction times h. Real-to-circle addition and triangle bounds
combine the THREE previously discharged errors at the SAME original N^-1
scale. The result holds for every h in SAME original U with SAME common M.
The fixed error budget is C_P+(D+1)*C_P+BinomialBudget(D)*B. This completes
the scalar stage, including the actual beta and paper alpha meanings.

7. Actual native application
Actual compact diagonal P has true degree<=ell and P(0)=0, using the original
weighted normalization and true logarithmic zero. Its value at one equals
the ORIGINAL diagonal real character of SAME normalized group first value,
proved by exact polynomial eval and genuine native Exp/Log character identity.
Every original combined relative coefficient, including index 1, transports
exactly through the Unit/univariate algebra equivalence and the COMPLETE
relative scalar formula. No new P/Q/sigma compatibility premise is assumed.

The native theorem composes the PREVIOUS actual dense nonlinear-separation
result with the complete generic scalar theorem. All inputs are discharged:
actual P/Q degree, actual P zero, M<=S, true nonempty useful U, h<N, actual
combined coefficient bounds and actual higher Q bounds. A single fixed
enlarged budget preserves BOTH higher P/Q tables, every original combined
relative coefficient bound and the true beta/alpha/sigma relation on SAME U.
The original fixed relative character list, norm, positive density, multiplier
bound and genuine large-N thresholds remain before ALL raw original source
coefficients/observations/sample lengths.

General degree still has ONE explicit inverse premise: the FULL desired
inverse on ACTUAL lower-degree relative-then-terminal child data. It is not
claimed already proved in all degrees. In degree TWO, actual child bound
is ONE, and the existing full degree-one inverse discharges that premise.
The degree-two theorem proves the actual quadratic P control and true
beta/alpha/sigma relation even though higher Q index range is empty. It is
UNIVARIATE, has true large-N conditions, and is NOT the degree-two original
nonzero inverse or a proof of StrongConjecture.

8. Next proof and a checked representative-choice issue
The remaining route is the actual bracket-polynomial alternative and original
horizontal-character reconstruction, or smaller rational filtration and
factorization for a reducible filtration. Degree induction alone is inadequate.

CURRENT actual representative choices in NativeRationalSelectedRepresentatives
are Classical choices from one compact coset set. Their actual lattice
factorization and global Log bound are proved. They are NOT stated to be a
canonical fractional-coordinate section. Thus rewriting sigma(h) immediately
as zeta dot fractional_part(gamma*h) would add an UNPROVED compatibility.
Next derive the actual horizontal/lattice coordinate relation and a fixed
finite bounded integer-offset refinement; thin the SAME useful shifts to
a common offset if necessary. This is further genuine proof work, not an
unavoidable obstruction. Do not change the original selected samples silently.

Also required: real commutator pairing coordinates/operator bounds, lattice
integrality/rational multiplication and nonzeroness of actual original
characters; true finite grid/operator/BOTH original raw coefficient bounds;
small-N completion, degree+nonlinearity induction and corrected multivariate
inverse. The separate interval Gowers correlation inverse, rough progressions,
cube/Alignment/positivity and final full separated FS/FP extraction remain open.

Author verification records: actual focused autoImplicit=false checks for all
new modules with empty logs; full root build; all registered axiom reports;
unchanged old proof hashes and axiom sets; Lean 4.32.2/mathlib/PNT+ pins and
six pinned OpenAI section hashes. Standard classical Lean only; no sorry,
admit, custom axiom, native computation or kernel bypass. Final raw logs are
authoritative. These are NOT independent kernel replay or external peer review.

Explicit judgments: original scope is addressed CONDITIONALLY as real
intermediate work; exact saved source passes author checks when confirmed by
final logs; does NOT fully solve the original problem; does NOT meet full
Lean completeness for an award submission. No unavoidable obstruction found.
Goal ACTIVE; no public repository/PR/prize application milestone reached.
'''
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
print(json.dumps(modules))
