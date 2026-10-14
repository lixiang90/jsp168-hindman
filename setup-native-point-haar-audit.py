from pathlib import Path
import json

prefix = 'round-native-point-haar'
old = 'round-native-rational-layer-haar'
modules = ['Hindman168/' + name + '.lean' for name in [
    'NativeSubgroupHorizontalLevelBridge', 'NativeRationalLayerLogPolynomial',
    'NativeRationalLayerPolynomialInverse', 'NativeSubgroupHorizontalTaylor',
    'NativeSubgroupTaylorTopCoefficient', 'NativeSubgroupHorizontalEscape',
    'NativeRationalLayerPointHaar']]
components = [
    'The ACTUAL initial rational subgroup horizontal character extends to the ambient model by the existing retraction. Original native differential bracket naturality and actual subgroup logarithm/lattice identities prove internal bracket annihilation, original rationality and a greatest nonzero level character. No horizontal or rational-character production assumption is added.',
    'Zero vector terms are removed using the proved exact zero-trim identity. The resulting actual restricted native log polynomial has ordinary degree at most the ORIGINAL filtration terminal index. Its COMPLETE scalar projection is exactly the original extended-character polynomial, so all monomial and binomial coefficients are retained.',
    'The unconditional original native polynomial inverse is now applied to the ACTUAL subgroup/conjugated lattice. One finite character grid and bound precede ALL original adapted sources, positive lengths and unit Lipschitz observables. Genuine discrepancy produces an original rational level character and BOTH complete original coefficient bounds.',
    'Internal horizontal scalarization commutes with the ACTUAL Taylor removal. A relative kernel ideal, not an ambient ideal assumption, proves log-product additivity. Lower removals preserve higher coefficients; terminal character kernels bound scalar degree; actual initial zeros identify the residual polynomial with its binomial factor.',
    'The degree-j monomial coefficient is EXACTLY the original order-j Taylor character value divided by j factorial. All-rational-level irrationality applies to that same character scaled by the nonzero rational reciprocal factorial, proving escape of the actual coefficient. No denominator is silently dropped.',
    'Finite intersections over the ACTUAL inverse character grid and original levels prove uniform q=0 point Haar convergence on the full unshifted integer interval for the ACTUAL irrational adapted source in the ACTUAL subgroup/conjugated-lattice quotient. This is a theorem from the exact irrationality output of the sequential factorization, not a newly supplied Haar assumption. Local boxes, progression restrictions, smooth-factor insertion and cubes are not inferred.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
    'Actual sequential smooth/irrational/periodic factorization and original subgroup horizontal-to-level '
    'transport are proved. The actual top scalar coefficient equals the original Taylor character value '
    'divided by its factorial; all-rational irrationality gives uniform q=0 Haar convergence on full '
    'unshifted integer intervals in the actual subgroup/conjugated-lattice quotient. Remaining: fixed-modulus '
    'progressions and local point boxes at positive scale fractions, smooth-factor Haar image transport; '
    'actual SAME-filtration cube subgroup geometry and face-character coefficient isolation, simultaneous '
    'local cube-Haar laws through ORIGINAL s+1, sequence limit BEFORE locality alpha->0, projected Haar '
    'face invariance/full-support coset symmetry, joint face lifts/full Alignment; separate arbitrary-input '
    'GTZ interval Gowers LINEAR nilsequence inverse at sufficient native step; final positive distinct '
    'rapidly separated SAME-color ALL nonempty FS AND FP. No Haar/source/character/period/inverse/bound '
    'oracle introduced. Author build/hash/axiom/source checks are not independent kernel replay or external '
    'peer review. No explicit delta-power law or other-marginal invariance is claimed. Public repository/PR/prize milestone not reached.')

for source, target in [('verification-manifest.json', prefix+'-baseline.json'),
                       ('lakefile.toml', prefix+'-lakefile-before.toml')]:
    target_path = Path(target)
    if target_path.exists():
        assert target_path.read_bytes() == Path(source).read_bytes()
    else:
        target_path.write_bytes(Path(source).read_bytes())
source = Path(old+'-audit.py').read_text(encoding='utf-8')
replacements = {'PREFIX=': prefix, 'OLD=': old, 'BASELINE=': prefix+'-baseline.json',
                'MODULES=': modules, 'COMPONENTS=': components, 'REMAINING=': remaining}
lines = []
for line in source.splitlines():
    key = next((key for key in replacements if line.startswith(key)), None)
    lines.append(key+repr(replacements[key]) if key else line)
source = '\n'.join(lines)+'\n'
source = source.replace(old+'-lakefile-before.toml', prefix+'-lakefile-before.toml')
Path(prefix+'-audit.py').write_text(source, encoding='utf-8')
Path(prefix+'-mathematical-review.txt').write_text('''Author mathematical review, 2026-10-14.
Primary reference: pinned OpenAI math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
07_cube_limits.tex, simultaneous local cube law proof, especially the maximal
character and isolated coefficient argument. This round proves q=0 on full
unshifted integer intervals. It does not prove the full local cube proposition.

1. The inherited unregistered horizontal bridge was explicitly recompiled.
Its subgroup is the original layer zero and its lattice is the actual
intersection with rho Gamma rho^-1. Native derivative/logarithm transport
is used; no ambient commutator-kernel claim is made.
2. Existing exact zero trim resolves a representation issue: weighted
lists may contain zero-vector terms of arbitrary scalar degree. Ordinary
degree is asserted only after trim. The original scalar projection is
preserved as a polynomial, not only at sampled points.
3. Inverse constants and finite character grid precede all sources and tests.
The inverse theorem is unconditional; source adaptation and geometric
filtration fields are its legitimate inputs, not replacements for an inverse.
4. The horizontal extension need only kill internal brackets. Its relative
kernel in layer zero is used in the actual BCH theorem. Higher original
monomial coefficients survive all lower Taylor removals exactly. The actual
residual has j initial zeros and scalar degree at most j; finite root
counting identifies it with value-at-j times the binomial polynomial.
5. The reciprocal factorial is explicitly rational and nonzero. The existing
all-rational-character irrationality includes this multiple; no invalid
real scalar invariance of circle norm is assumed.
6. The finite character/level intersection produces ONE eventual threshold
for ALL unit Lipschitz tests, including tests depending on the sequence index.
The finite list may be empty and ell may be zero: then discrepancy cannot
produce the required character/positive level, so no fake witness is chosen.
7. The source sampling is literally scalarMvIntegerCube Unit N = [0,N).
N is any cofinal natural length sequence. The irrationality scale in this
theorem is exactly N. Floor/real-length transport, shorter windows,
translations and fixed rational/integer progression factors require further
proof and are not part of this theorem.
8. No full Hindman theorem, independent review, award eligibility or
unavoidable obstruction is asserted. Full source/hash/axiom/build checks
remain author-side checks and do not constitute independent kernel replay.
''', encoding='utf-8')
sync = json.loads(Path('openai-math-sync-2026-10-13.json').read_text())
sync.update(checked_date='2026-10-14', method='Authenticated GitHub connector fetch_commit(main)',
            conclusion='Remote main remains 1581d4cbdd69a0faf34b2089614fe2a814316a6a. No source change since previous remote check. Pinned sections also verified against local Git objects by the round audit.')
Path('openai-math-sync-2026-10-14.json').write_text(json.dumps(sync, indent=2)+'\n')
print(prefix)
