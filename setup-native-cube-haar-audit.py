from pathlib import Path
prefix = 'round-native-cube-haar'
old = 'round-native-cube-filtration'
modules = ['Hindman168/'+name+'.lean' for name in [
'NativeResidueCubeOrbit','NativeResidueCubeHaarImage','NativeNilmanifoldProbabilityFullSupport',
'NativeResidueCubeHaarInvariance','NativeResidueCubeHaarSupport']]
components = [
'Constructed the actual rational-residue cube orbit map into ORIGINAL vertex coset spaces, with representative formula (h x_V rho Gamma)_V. Proved exact lattice vertex membership, well-definedness, injectivity, continuity and compact range.',
'Constructed the Haar image by pushing the actual normalized native quotient probability to these ORIGINAL vertex cosets. Proved probability and concentration on the actual orbit without any empirical limit assumption.',
'Proved the actual normalized native quotient probability positive on EVERY nonempty open set, using its established invariance and compact transitive coset action.',
'Proved exact equivariance of the original vertex orbit map for every actual cube-group element, with vertex action conjugated by h. Derived invariance of the Haar image under this full cube-group action from the actual quotient invariant probability.',
'Proved the actual cube orbit is a closed embedded compact quotient. Proved an ambient open set has positive Haar-image mass IFF it meets this actual orbit, identifying its full support with no supplied support or Haar oracle.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
'Original q=0 weak probability limit and all-continuous tests, SAME-filtration actual native cube group, '
'FULL rational cube filtration, rational-residue cube data, actual original vertex orbit and Haar '
'probability image with full cube invariance and EXACT full support are proved, preserving original '
'step s and degree. Remaining: face-character coefficient isolation and original source cube '
'adaptation; simultaneous local cube laws through ORIGINAL s+1 with length before locality; '
'projected face invariance/full support, joint lifts/full Alignment; separate arbitrary-input GTZ '
'interval Gowers LINEAR nilsequence inverse; final positive distinct rapidly separated SAME-color '
'ALL nonempty FS AND FP. No source/Haar/inverse oracle or new axiom introduced. Author checks are '
'not independent kernel replay or external peer review. Public repository/PR/prize milestone not reached.')
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
Pinned OpenAI section 7, definition of Haar measure on rational cube cosets.

The source is nativeResidueCubeData from the preceding round: the SAME
actual cube subgroup with lattice intersection of product(rho Gamma rho^-1).
The orbit target is Finset(Fin d) -> ORIGINAL G/Gamma. On representatives
the map is exactly x -> (h x_V rho Gamma)_V. Lattice membership is equivalent
to all vertices being in rho Gamma rho^-1. This proves well-definedness by
the original left-coset equivalence, and conversely proves injectivity.
No normality of Gamma is used. Actual product-coordinate continuity and
quotient-lift continuity prove continuity; source compactness proves compact
range. Original discrete-lattice quotient is Hausdorff, so this is a CLOSED
embedding of the actual quotient, not just a parameterized image.

The Haar image is Measure.map of nativeNilmanifoldQuotientProbability of
the actual residue cube data. This source measure was constructed from the
actual original Lie-group Haar measure and positive finite fundamental
domain, with probability and invariance already proved. Measurability uses
the natural coset Borel structure; finite vertex products use the proved
Polish original group and its second-countable quotient. No change to the
metric or topology is made. Probability and concentration are proved.

For y in the cube group, the target action at vertex V is left translation
by h y_V h^-1. On representatives this sends h x_V rho Gamma to
h (y x)_V rho Gamma. Exact group-coordinate multiplicativity proves the
intertwining identity; source Haar invariance and composition of measure
pushforwards prove image invariance for EVERY cube-group y.

For any native compact coset probability, group-action invariance and the
transitive coset action imply positivity on nonempty opens: a finite set
of translates covers the compact quotient. This is supplied by the checked
general mathlib minimal-action theorem with K=univ and probability mass 1.
Applied to the ACTUAL residue cube source, the preimage of an open set is
nonempty exactly when that open set meets the orbit. The map formula and
source positivity prove positive image mass IFF the open set meets the
orbit. Combined with its closed compact range, this identifies full support.
This is support on the original cube orbit, not on all ambient vertex cosets.

No empirical equidistribution follows just from constructing this measure.
Original source cube adaptation, largest surviving face character and
isolated top coefficient, simultaneous local laws, projected face symmetries,
joint lifts/Alignment, arbitrary-input GTZ inverse and final same-color
FS/FP remain outstanding. StrongConjecture remains UNPROVED. No unavoidable
obstruction established. Author checks are not independent kernel replay
or external peer review; publication/PR/prize milestone remains pending.
''', encoding='utf-8')
print(prefix)
