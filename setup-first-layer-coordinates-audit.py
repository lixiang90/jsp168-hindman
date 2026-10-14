from pathlib import Path
import json
import re

prefix = 'round-native-rational-first-layer-coordinates'
old = 'round-native-rational-paper-scalar-separation'
base = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained = {f['path'] for f in base['files']}
modules = sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules) == 13, modules
components = [
    'ACTUAL rational split basis of original model relative to TRUE filtration layer F_2 is CONSTRUCTED. Its rational first-layer duals are proved to be actual real basis coordinates and to kill SAME F_2. Rationality is discharged from the actual lattice rational log span and filtration rationality, not supplied as an abstract coordinate oracle.',
    'ONE geometry-only positive NATURAL denominator is CONSTRUCTED from a finite rational coordinate matrix on the actual original lattice smooth basis. Every scaled first-layer coordinate is proved integral on SAME original lattice. Genuine G/F_2 coordinate map is continuous/additive with exact integer-power identity and kernel EXACTLY actual original F_2, not merely the lower-central commutator layer.',
    'EVERY real original functional killing TRUE F_2 is exactly evaluated in these scaled first-layer coordinates using actual rational split-basis values divided by SAME fixed denominator. Empty first-layer index cases are included; no surjectivity of the lattice image onto all Z^m is asserted.',
    'The genuine relative commutator observable is continuous and vanishes on actual F_2 in its second input, PROVED from actual relative horizontality, F_2 additivity and whole-group conjugation invariance. Continuous real-character linearization gives a TRUE original functional killing F_2 and the exact commutator coordinate formula, with actual coefficients evaluated on fixed original exponential split-basis points.',
    'Actual compact selected representatives have geometry-only bounded true first-layer coordinates. Their coordinates equal fractional parts of actual group coordinates PLUS actual integer floor offsets, derived from SAME actual original lattice factorization and proven lattice integrality. ALL offsets lie in ONE fixed finite integer box preceding every source polynomial/group element/shift/sample; representatives are never assumed canonical fractional sections.',
    'SAME actual useful shifts admit a nonempty subset with ONE common actual integer-offset vector from that fixed finite box. Explicit card(U)<=card(C)*card(V) retains the density loss, and V is a SUBSET of U. Exact selected representative coordinates are fractional_part(h*H(a))+b on V. No original sample or actual selected representative is replaced.',
    'The actual compact normalized original commutator slope sigma(h) is exactly rewritten on SAME refined V as sum zeta_i*fractional_part(h*gamma_i)+sum zeta_i*b_i. The genuine common multiplier M is absorbed algebraically into zeta/alpha/beta including actual beta offset correction. The native application uses SAME original compact normalized polynomial first value and SAME shift representatives; no bracket-polynomial inverse is assumed.',
    'TRUE original nonzero integer vectors produce ACTUAL original horizontal characters which kill F_2 and are lattice-integral. Nonzeroness follows from evaluation on actual split-basis columns and positivity of SAME common denominator. A fixed coordinate operator budget bounds the character and places it in the existing ORIGINAL finite horizontal grid whenever integer coefficients are bounded. Producing such a vector from the signal remains OPEN.',
    'Actual commutator coefficient norm budget is PROVED by continuity of the genuine relative commutator model on SAME fixed compact representative set and finite split-basis points. Budget precedes ALL characters and raw original coefficients. Actual compact normalized first value belongs to SAME set, so |zeta_i|<=norm(chi)*B is applied to actual compact source polynomial, without a compatibility or bounded-source premise.'
]
remaining = base['last_round']['remaining']
remaining += '\nLATEST TRUE FIRST-LAYER MILESTONE: Actual G/F_2 lattice-integral coordinates, exact kernel/powers/real-character evaluation, commutator factoring, geometry-only zeta budget, actual fractional-coordinate-plus-integer-offset identity, fixed finite offset box, SAME-useful-shift dense common-offset refinement, exact actual compact sigma bracket expression and original integer-character nonzero/horizontal/lattice/operator/grid properties are PROVED. This resolves the arbitrary compact representative compatibility issue; it does NOT produce the integer vector required by Claim 7.7 or close original inverse. NEXT: transport the PROVED beta/alpha/sigma circle relation and useful-density through SAME offset refinement, retain bounded M/relative character/coefficient budgets, and prove actual Claim 7.7 quantitative bracket alternative. Then actual original character coefficient reconstruction OR smaller rational nonlinearity filtration/factorization and genuine degree+nonlinearity induction, small-N completion, corrected multivariate inverse, interval Gowers correlation inverse, rough progressions, Alignment and StrongConjecture. Lattice coordinate image is only proved contained in Z^m, not asserted equal to Z^m. No unavoidable obstruction found; publication/application milestone not reached.'
text = Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
    text = re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),text,flags=re.M)
text = re.sub(r'^"""Audit .*?\n', '"""Audit genuine first-layer coordinates and actual compact fractional commutator refinement.\n', text, count=1)
text = re.sub(r"reference_scope='[^']*'", "reference_scope='OpenAI 06_rough_progressions quantitative Leibman route; Green-Tao section 7 actual first-layer/commutator/fractional-offset input before Claim 7.7; bracket alternative and full inverse remain open'",text)
Path(prefix+'-audit.py').write_text(text,encoding='utf-8')
review = '''JSP-000168 / Erdos #172: TRUE first-layer coordinates and compact fractional refinement
Author mathematical review, 2026-10-13. Verdict: Partial coverage.
NOT independent kernel replay or external peer review.

Original prize target: every finite coloring of positive integers admits
arbitrarily large positive distinct monochromatic finite-sums/finite-products
witnesses. StrongConjecture remains UNPROVED. No unavoidable obstruction found.
Pinned original OpenAI six-section source:
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026,
06_rough_progressions. Auxiliary route: https://arxiv.org/html/0709.3562v4 ,
section 7, equations 7.10-7.11 / Claim 7.7. Corrected multivariate scope:
https://arxiv.org/html/1311.6170v3 . This round establishes actual inputs
needed before that claim; it does NOT prove the quantitative alternative.

1. Actual F_2 versus commutator layer
Subsequent original characters must kill ACTUAL F_2 so that the filtered
polynomial orbit becomes linear in these coordinates. A character killing
only [G,G] would not supply this property for a general rational filtration.
The new construction splits the actual original rational lattice log span
along its intersection with L.layer(2). The filtration rationality theorem
proves that the real span of the inl columns is EXACTLY L.layer(2).
The inr rational basis-coordinate duals extend to genuine real functionals,
and equality with the actual split-real-basis coordinates is proved.

2. Actual denominator and original lattice
Evaluate every first-layer rational dual on every vector of the actual
original filtered smooth lattice basis. These form a FINITE rational matrix.
The product of rational denominators gives one positive natural multiplier
for all entries. Each scaled functional kills F_2 and hence [G,G]. The
existing native lattice integrality equivalence on the actual smooth basis
then PROVES integrality on every element of SAME original lattice Gamma.
No assertion that exponential split-basis points lie in Gamma is made.
The image H(Gamma) is proved CONTAINED in Z^m, not necessarily equal to Z^m.
That inclusion suffices for the actual fractional-coordinate identity.

3. Exact actual first-layer map
H(g) consists of scaled duals evaluated on the original native Log(g).
Native Log-character multiplication gives H(gh)=H(g)+H(h); a genuine
multiplicative homomorphism into Multiplicative(Pi R) proves the exact
integer-power law H(a^h)=h H(a). Continuity follows from the actual Log and
finite-dimensional linear maps. The real split-basis expansion proves
ALL inr coordinates vanish IFF Log(g) belongs to L.layer(2), hence
ker H is EXACT original filtered group F_2. The empty first-layer index
case is also covered by these basis and finite-sum proofs.

4. Genuine commutator linearization
For psi, the actual relative F_2 difference real character, relative
horizontality has ALREADY proved psi additive and invariant under
conjugation by every original g. If w belongs to F_2, [a,w] equals
conjugate(a,w)*w^-1 IN THE SAME actual subgroup. Additivity, invariance and
the exact inverse identity therefore PROVE psi([a,w])=0.
For fixed a, g -> psi([a,g]) is continuous by actual group operations,
subtype continuity and the native relative Log. Existing actual continuous
real-character linearization produces an original continuous linear f,
and evaluating at Exp(v) for v in L.layer(2) PROVES f kills F_2.
Actual basis expansion then gives
  psi([a,g]) = sum_i zeta_i * H(g)_i,
  zeta_i = psi([a,Exp(b_inr_i)]) / q.
Every exponential and coefficient is the true native original/relative
value. No whole-group extension of psi itself is asserted. No nonzero
zeta_i is inferred from nonzeroness of the original relative character.

5. Geometry-only coefficient budget
The actual model Log_relative(firstDifference([a,Exp(b_i)])) is proved
continuous in a. Its finite vector of norms is continuous; compactness of
the SAME chosen representative set bounds every such norm by one B>=0.
Operator norm gives |chi(v)|<=norm(chi)*norm(v). q>=1 controls division,
so every |zeta_i|<=norm(chi)*B on that set, before all chi and source data.
The PROVED exact normalized first-value identity places actual compact
polynomial a=P_0(1) in SAME chosen set. The bound is applied to this a.

6. Actual compact representative issue resolved
The original compact representatives were arbitrary Classical choices;
they have NEVER been assumed a fractional-coordinate section. Compactness
and continuity of H give a uniform bound |H(t)_i|<=B_H. Actual factorization
g=t*gamma and PROVED H(gamma)_i in Z give fract H(g)_i=fract H(t)_i.
Consequently H(t)_i=fract H(g)_i+b(g)_i, where b(g)_i=floor H(t)_i is the
ACTUAL integer offset. Bounds 0<=fract<1 prove -B_H-1<=b_i<=B_H+1.
Choose one natural K>B_H+1 BEFORE all g. The finite Pi box [-K,K]^m is
nonempty and contains EVERY actual offset vector. Zero-dimensional cases
remain included. No canonical representative or sample substitution occurs.

7. SAME useful shifts and exact fractional slope
For any actual nonempty U, finite witness selection on the fixed box gives
one b and V subset U, V nonempty, card U <= card C * card V. On V,
H(selected_rep(a^h))=fract(h H(a))+b, coordinate by coordinate.
Combine this with the PROVED commutator representation to obtain
sigma(h)=sum zeta_i*fract(h gamma_i)+sum zeta_i*b_i.
The theorem is APPLIED to the SAME original normalized polynomial P_0,
actual a=P_0(1), actual selected shift representatives, and SAME compact
commutator slope used in the previously proved paper scalar separation.
Exact distributivity proves that multiplying by M gives zeta'=M*zeta,
alpha'=M*alpha and beta'=M*beta+sum zeta'_i*b_i. M is not assumed to
preserve small norms for arbitrary real multiplication; this statement is
an EXACT real identity used with the previously proved NATURAL multiplier.
Transport of the actual useful-density/circle-bound package is next.

8. Actual candidate original character
For any integer vector k, f_k=sum k_i * (q-scaled dual_i) is a genuine
original continuous linear functional. It kills ACTUAL F_2, and its values
on Log(Gamma) are integer finite sums. Evaluating at b_inr_j gives q*k_j.
q>0 proves k != 0 implies f_k != 0. Together these establish the actual
original horizontal-character predicate. The coordinate operator sum gives
norm(f_k)<=R*sum_i norm(coord_i) when |k_i|<=R. Existing original-grid
completeness places f_k in the ORIGINAL fixed horizontal grid for R>=0.
The claim does NOT produce k from the signal or prove original polynomial
coefficient bounds; those remain part of the quantitative alternative and
reconstruction. A nonzero relative character alone does not supply k.

9. Scope and remaining work
All this round's coordinate, compactness, integrality and algebraic results
have NO child inverse premise. Their application to the full previously
proved general-degree useful-shift signal still retains that signal's FULL
desired lower-degree child inverse premise. The degree-two scalar stage
discharges that child premise but still does not close the original inverse.
Next prove quantitative Claim 7.7 and actual original character coefficient
reconstruction OR smaller rational nonlinearity filtration/factorization,
then degree+nonlinearity induction, small-N completion, corrected multivariate
inverse, separate interval Gowers correlation inverse, rough progressions,
Alignment/positivity and final original FS/FP theorem. This finite-offset
correction addresses a proof compatibility issue, not an unavoidable barrier.

All old registered proof-source hashes/selected axiom sets are retained.
New modules are to receive explicit autoImplicit=false checking with empty
logs, full build and expanded selected axiom scan, with every final process
awaited to terminal success before recording verification. Allowed axioms
are only propext, Classical.choice and Quot.sound; no sorry/admit, custom
axiom, unsafe implementation or native_decide bypass is allowed.
Public repository/PR/prize application milestone has NOT been reached.

10. Fresh primary-source review of the next step
Claim 7.7 has two actual alternatives: a bounded nonzero integer multiplier
makes every zeta coordinate close to an integer, OR a bounded nonzero integer
vector makes k dot gamma small. The first alternative is NOT already a
smaller filtration. The source applies Proposition 5.3 twice, first after
adjoining the alpha coordinate, then after an integer correction. This
quantitative argument remains UNPROVED here.

Two explicit continuation cautions arise from our chosen geometry:
(a) split-basis Exp(b_i) points are not asserted lattice elements. A future
commutator character using them needs its own lattice-integrality proof or
extra genuine rational denominator; the new q-scaled dual integrality does
not automatically prove integrality of every commutator functional.
(b) Int.fract is the [0,1) fractional part. Small circle norm does NOT imply
small absolute Int.fract; the next alpha residual must subtract an actual
nearest integer rather than assuming this false implication.
Both are manageable proof obligations, not established unavoidable barriers.
'''
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
print(json.dumps(dict(prefix=prefix,modules=modules),ensure_ascii=False))
