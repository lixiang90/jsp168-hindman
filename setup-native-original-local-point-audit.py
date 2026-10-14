from pathlib import Path

prefix = 'round-native-original-local-point'
old = 'round-native-smooth-local-haar'
modules = ['Hindman168/'+name+'.lean' for name in [
    'NativeRationalLayerHaarContinuity', 'SignedProgressionResidue',
    'NativeOriginalResidueLocalHaar', 'NativeOriginalIntervalLocalHaar',
    'RealIntervalResidueGeometry', 'NativeOriginalRealLocalHaar',
    'NativeSequentialOriginalLocalPointLaw']]
components = [
    'Expectations of the ACTUAL original subgroup Haar image vary continuously along every continuous locally compact first-countable parameter family of left factors. This uses actual compact subgroup probability and joint orbit continuity, with original integral transport; no empirical-limit assumption.',
    'Fixed-period signed progressions have exactly constant original residues whenever the period divides their nonzero signed step. The exact original factorization identity removes the actual lattice gamma and freezes the right factor to the actual rational sigma. A finite intersection yields ONE threshold for ALL residue classes, origins, lengths and unit tests.',
    'The original local law now covers ACTUAL integer interval residue sets. Their exact existing progression enumeration and proved count discrepancy give positive-fraction progression lengths and nonemptiness. No endpoint/tail/cardinality hypothesis is supplied as an oracle.',
    'Real half-open windows are defined with exact ceil endpoints and proved membership, length error below one, and residue count error at most 1+1/M. The original local law is instantiated at the paper windows [beta*L,(beta+alpha)*L), with ALL residues and unit tests after one length threshold for each fixed alpha. Length limit precedes alpha shrinking.',
    'From any ORIGINAL adapted polynomial sequence and original cofinal real length, a proved theorem constructs ONE subsequence, SAME final rational subgroup filtration subordinate to the input filtration, one positive period, actual rational residue representatives and ONE smooth curve. It simultaneously supplies original signed-progression and real-window q=0 local Haar laws and continuous expectations of those SAME original Haar images.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
    'Original adapted sequences now have actual q=0 local point Haar laws on one subsequence, with SAME '
    'final filtration/period/smooth curve, exact original signed residues and real paper windows, proved '
    'endpoint/cardinality bounds and continuous original Haar expectations. Remaining: global Riemann '
    'point-mixture assembly; actual SAME-filtration cube subgroup geometry and face-character coefficient '
    'isolation, simultaneous local cube laws through ORIGINAL s+1 with length before locality, projected '
    'face invariance/full support, joint lifts/full Alignment; separate arbitrary-input GTZ interval Gowers '
    'LINEAR nilsequence inverse; final positive distinct rapidly separated SAME-color ALL nonempty FS AND FP. '
    'No source/Haar/geometry/inverse oracle or new axiom introduced. Author checks are not independent '
    'kernel replay or external peer review. No global metric Lipschitz or quantitative locality rate claimed. '
    'Public repository/PR/prize milestone not reached.')
for source, target in [('verification-manifest.json', prefix+'-baseline.json'),
                       ('lakefile.toml', prefix+'-lakefile-before.toml')]:
    path = Path(target)
    if path.exists():
        assert path.read_bytes() == Path(source).read_bytes()
    else:
        path.write_bytes(Path(source).read_bytes())
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
Pinned OpenAI 07_cube_limits.tex: q=0 of Proposition local-cube-law, exact
periodic cosets, actual local windows, and continuity of Haar expectations.
This is NOT positive-dimensional cube laws, global point mixture or final FS/FP.

The continuity proof integrates a genuinely jointly continuous pullback over
the compact original subgroup quotient with its actual probability. Explicit
native metric/Borel structures match the earlier integral transport. The
parameter assumptions of the generic theorem hold for R and the actual
smooth curve. No extra Haar law or weak-continuity oracle is assumed.

Signed arithmetic is exact for positive period M and ANY signed integer d
divisible by M, including negative d. The nonzero-step condition is retained
where inverse equidistribution is applied. Original source identities are
at all real inputs; actual lattice gamma is removed using the existing
right-coset identity, WITHOUT assuming the lattice normal. Unit-coordinate
reparametrization and integer/rational/real casts are explicitly checked.
There is one curve and radius for all rational representatives. A finite
intersection over Fin M occurs BEFORE all varying origins/windows/tests.

NativeResidueLocalHaarLaw and NativeRealLocalHaarLaw are proposition
abbreviations for the displayed conclusions, not input structures carrying
unproved analytic assertions. The top assembly theorem PROVES both directly
from original adaptation/cofinality using the existing native factorization.
The generic transport helpers take proved earlier conclusions as hypotheses.

For integer intervals, exact enumeration gives the true residue cardinality
m. The discrepancy |m-T/M|<=1 and eventual L>=2*M/kappa give
m>=kappa*L/(2*M)>0. The actual first progression sample is therefore in the
requested residue class, identifying its Haar image; all samples belong to
the original integer window. Exact mean identities incur no boundary loss.

For real endpoints a<=b, the integer window has endpoints ceil(a),ceil(b).
Its membership is exactly a<=z<b, its length differs from b-a by less than
one, and each residue count differs from (b-a)/M by at most 1+1/M. Empty and
negative-endpoint windows cause no silent truncation; native applications
derive eventual nonemptiness from positive alpha and cofinal original L.

NativeRealLocalHaarLaw quantifies beta,epsilon, then alpha0>0, then EVERY
FIXED 0<alpha<alpha0, then an eventual sequence threshold, then ALL residues
and unit tests. This is the epsilon form of the required length-first,
locality-second convergence. It does not allow alpha to vanish with n before
taking the length limit. No uniform radius over all beta or O(alpha) rate
in an arbitrary compatible metric is claimed. Global point-mixture assembly
must still justify finite partition/freezing and its threshold order.

The original source theorem uses ONE existing factorization witness and
retains its exact H and period. It asserts only q=0. Future joint cube work
must use this SAME witness; independently obtaining unrelated q-filtrations
would not prove the paper's simultaneous theorem. Original ambient step s
and input degree are not replaced.

Still missing: Riemann global point mixture, native cube geometry and source
coefficient isolation through original s+1, projected face Haar invariance
and full support, joint lifts/full Alignment, separate GTZ inverse and final
same-color ALL nonempty FS and FP with positive distinct rapid separation.
No unavoidable obstruction established. Author checks are not independent
kernel replay or external peer review; no publication or prize claim made.
''', encoding='utf-8')
print(prefix)
