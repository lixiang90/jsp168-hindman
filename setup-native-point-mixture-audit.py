from pathlib import Path

prefix = 'round-native-point-mixture'
old = 'round-native-original-local-point'
modules = ['Hindman168/'+name+'.lean' for name in [
    'CompactGaugeUniformMesh', 'CompactGaugeFiniteOscillation',
    'RealMeshResiduePartition', 'ComplexTaggedMeshIntegral',
    'FiniteComplexCellMassError', 'RealMeshComplexAverage',
    'NativeOriginalTaggedPointMesh', 'NativeOriginalScaledPointMixture',
    'ComplexFloorWindowTransfer', 'NativeOriginalPointMixture']]
components = [
    'An arbitrary strictly positive beta-dependent local gauge on [0,1] admits an actual finite uniform mesh with fixed tags subordinate to that gauge, by compactness and a Lebesgue number. The same mesh can control a finite continuous family of Haar expectations. No uniform lower bound on the original gauge is assumed.',
    'The original integer ceil-window sum is EXACTLY partitioned into real-mesh cells and all signed residue classes. Direct interval-integral splitting and actual oscillation bounds prove the tagged integral error. Meshes/tags are fixed BEFORE every eventual sequence threshold.',
    'True cell cardinalities have normalized error at most 2/L from 1/(N*M). Exact mean-times-cardinality identities retain BOTH local mean error and mass error, proving the whole ceil-window real-normalized error epsilon+2*N*M*(epsilon+1)/L.',
    'The original source, same rational residue Haar images and continuous smooth curve satisfy the global real-normalized point-mixture formula for EVERY unit Lipschitz test. Meshes may depend on the test and tolerance but the source subsequence and all factorization data do not.',
    'The exact floor-window mean differs from the ceil-window sum divided by real L by at most 2/L for any unit-bounded input, including both the at-most-one-point boundary and the denominator change. Thus the ORIGINAL sequential adapted source now satisfies the paper floor(L) point-mixture formula in unit-Lipschitz test form, retaining its SAME local laws, final filtration, positive period, actual sigma and smooth h.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
    'Original q=0 local laws and the global floor-window point-mixture formula in UNIT-LIPSCHITZ TEST FORM '
    'are proved on one original subsequence with SAME final filtration/period/sigma/h. Remaining: package '
    'the actual probability mixture and weak-measure convergence/all-continuous testing as required by '
    'later joint-law interfaces; actual SAME-filtration cube subgroup geometry and face-character coefficient '
    'isolation, simultaneous local cube laws through ORIGINAL s+1 with length before locality, projected '
    'face invariance/full support, joint lifts/full Alignment; separate arbitrary-input GTZ interval Gowers '
    'LINEAR nilsequence inverse; final positive distinct rapidly separated SAME-color ALL nonempty FS AND FP. '
    'No Haar/source/cardinality/partition/inverse oracle or new axiom introduced. Author checks are not '
    'independent kernel replay or external peer review. No global metric Lipschitz or quantitative locality '
    'rate claimed. Public repository/PR/prize milestone not reached.')
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
Pinned OpenAI 07_cube_limits.tex: equation joint-point-law and its final
finite partition/Riemann argument. Proved here in unit-Lipschitz test form
on the ORIGINAL source and paper floor(L) window. This is NOT the whole
simultaneous positive-dimensional cube proposition or final FS/FP theorem.

The prior local radius depends on beta. It is not silently replaced by a
uniform lower radius. The actual positive gauge defines an open ball cover
of compact [0,1]; a proved Lebesgue number yields a finite uniform mesh.
Tags can lie outside their cells, but every point of the closed cell lies
within the tag's allowed radius. All tags remain in [0,1]. The existing
local theorem permits arbitrary intervals within that radius, so no invalid
one-sided endpoint freezing is used. Finite continuous expectation families
are included by intersecting their actual continuity neighborhoods.

For a FIXED observable and tolerance, mesh N and finitely many tags are
chosen before all length thresholds. The finite eventual intersection over
tags is valid. No further subsequence is selected, and no sequence-dependent
tag or mesh is introduced. True rounded cell lengths exceed L/(2*N) once
L>=2*N, so the previous local laws apply to actual nonempty residue cells.

Exact signed-residue sums and monotone integer cuts partition Ico 0 ceil(L).
The cardinality error |card/L-1/(N*M)|<=2/L is derived from existing true
real-endpoint residue counts, not an asymptotic oracle. The finite cell
error retains both local mean deviation and actual mass deviation. Empty
sets do not invalidate the mean-times-card identity. At fixed mesh the
mass error tends to zero by the ORIGINAL real cofinality.

Tagged integral error is proved directly by integration of each cell's
oscillation, using continuous expectations and exact adjacent interval
integral sums. It does not assume Riemann-sum convergence. The original
Haar-image probability proves expectation norm<=1 for unit tests. Finite
averaging over M residues gives exactly the paper factor 1/M.

The real-normalized result is converted to the PAPER window Ico 0 floor(L).
The actual integer tail Ico floor(L) ceil(L) has at most one point. Its sum
norm is <=1. The denominator change contributes at most 1/L using the actual
floor-card identity, 0<=L-floor(L)<1 and the unit mean bound. Total <=2/L.
Thus neither integrality of L nor equality of ceil and floor is assumed.
All small/zero floor cases satisfy the finite identity; eventual cofinality
supplies positive paper denominators for the final limiting application.

The final sequential theorem starts with original D,F,L,p and adaptation,
uses ONE previously constructed factorization witness, and returns its SAME
subsequence, subordinate H, positive M, rational sigma, smooth h, both local
laws and global UNIT-LIPSCHITZ test limits. Unit tests are a standard weak
convergence determining class on this compact metric quotient, but this
round does NOT yet package the actual probability mixture or formally prove
the all-continuous/weak-measure API. That remains explicit work, not a claim
that the entire paper proposition has been finished.

Still missing: probability/joint-law packaging, positive-dimensional actual
native cube geometry/coefficient isolation through original s+1, projected
face Haar invariance/full support, joint lifts/full Alignment, separate GTZ
inverse, and final SAME-color ALL nonempty FS and FP with original positivity,
distinctness and rapid separation. No unavoidable obstruction established.
Author checks are not independent kernel replay or external peer review.
No publication/prize completion claim is made.
''', encoding='utf-8')
print(prefix)
