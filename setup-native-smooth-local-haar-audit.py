from pathlib import Path

prefix = 'round-native-smooth-local-haar'
old = 'round-native-window-haar'
modules = ['Hindman168/'+name+'.lean' for name in [
    'NativeRationalLayerCompactWindowHaar', 'NativeRationalLayerOrbitObservables',
    'NativeRationalLayerFrozenHaar', 'CompactSequentialParameterFreezing',
    'NativeSmoothActionFreezing', 'NativeRationalLayerSmoothLocalHaar']]
components = [
    'Actual subgroup REAL-scale translated progression window laws now hold uniformly on ANY fixed compact family of continuous observables, via proved finite unit-Lipschitz detectors chosen before all sources, origins and window lengths.',
    'The actual original orbit action is jointly continuous in compatible metrics. Pullback of original continuous observables along this action is continuous in the compact-open topology, hence compact original tests and compact left factors give a compact subgroup test family. Original Haar-image integrals equal these subgroup integrals.',
    'Frozen left-factor window laws target the canonical ORIGINAL subgroup Haar image, uniformly over compact original tests and compact original left factors. No global Lipschitz assumption about arbitrary compatible metrics is used.',
    'The actual converging finite-dimensional smooth parameters yield uniform freezing over the ENTIRE original compact quotient. The limiting curve is genuinely manifold-smooth. Only joint continuity and compactness are used for the quotient-action error modulus.',
    'The actual smooth-times-irrational source satisfies a q=0 LOCAL Haar law in the original quotient. The smooth curve is chosen once; each beta and epsilon determines a positive radius BEFORE ALL rational right factors, every fixed nonzero rational progression step and positive window fraction. For each fixed right factor and fraction the eventual length threshold precedes all permitted origins, windows and unit-Lipschitz tests. Original real scale positivity is derived from cofinality.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
    'Actual factorization, original subgroup q=0 Haar windows, compact observable transport, original Haar-image '
    'integrals and actual smooth-factor LOCAL q=0 Haar law are proved. Remaining: instantiate exact original '
    'periodic residues and progression endpoint/cardinality estimates, continuous Haar-image dependence and '
    'Riemann point-mixture assembly; actual SAME-filtration cube subgroup geometry and face-character coefficient '
    'isolation, simultaneous local cube laws through ORIGINAL s+1 with length before locality, projected face '
    'invariance/full support, joint lifts/full Alignment; separate arbitrary-input GTZ interval Gowers LINEAR '
    'nilsequence inverse; final positive distinct rapidly separated SAME-color ALL nonempty FS AND FP. '
    'No source/Haar/geometry/inverse oracle or new axiom introduced. Author checks are not independent kernel '
    'replay or external peer review. No global metric Lipschitz or quantitative locality rate claimed. '
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
Pinned OpenAI 07_cube_limits.tex, q=0 part of simultaneous local cube law,
particularly inserting the smooth factor after subgroup equidistribution.
This is NOT the full simultaneous local cube law or final Hindman theorem.

Compact test-family detection is applied to the actual subgroup quotient
with its actual conjugated lattice, source and probability. It upgrades the
already proved unit-test law; it does not assume the desired Haar limit.
All detector thresholds precede every origin and window, so sample-dependent
tests within one fixed compact family are genuinely allowed.

The original orbit map h*x*rho Gamma is jointly continuous. Equality of
natural and compatible-metric topologies is explicitly transported at BOTH
quotients. Continuous currying on the compact subgroup quotient gives the
actual compact pullback family. Integral transport is the actual measurable
pushforward formula with verified Borel structures. The lattice is never
assumed normal.

Arbitrary compatible metrics need not make left actions globally Lipschitz.
The freezing proof instead uses joint continuity, compactness of the original
quotient, and convergence of actual finite-dimensional smooth parameters.
The generic parameter lemma states its uniform-space and weak local
compactness requirements explicitly; these hold for the native parameter
space, rather than becoming additional assumptions of the native theorem.
The limiting curve is constructed from the genuine smooth binomial family
and exponential. It is chosen ONCE for all beta, errors, rational right
factors, steps and windows. Review strengthened the theorem so that right
factors are quantified AFTER this curve and locality radius; different
residue classes therefore cannot silently choose different curves.

The local theorem uses epsilon/3 for freezing and epsilon/3 for frozen Haar.
The finite-mean error bound is valid even for an empty set; the actual
window lower bound and eventual L>0 make windows nonempty in applications.
Normalization L*((b+d*x)/L)=b+d*x uses eventual strict positivity derived
from original cofinality. Every sampled normalized input must lie within
the selected radius. No false unbounded-window smooth approximation is used.

Quantifiers: h, then beta and epsilon, then positive radius, then arbitrary
FIXED rational right factor, rational nonzero step and positive fraction
tau<=1, then eventual
length threshold, then all origins/windows/unit tests. This supplies the
epsilon criterion needed for taking the length limit FIRST for each fixed
small locality. It does not assert uniformity as tau tends to zero before
the length limit. No linear O(alpha) rate in an arbitrary metric is claimed.

Still missing: exact original residue assembly and explicit progression
endpoints/cardinalities, global Riemann point mixture, genuine positive-
dimensional native cube geometry and source, all later symmetry/alignment,
the separate arbitrary-input GTZ inverse, and final all-FS/all-FP theorem.
No unavoidable obstruction established. No independent kernel replay or
external peer review is claimed. No public/prize completion claim is made.
''', encoding='utf-8')
print(prefix)
