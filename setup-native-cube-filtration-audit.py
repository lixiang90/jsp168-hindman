from pathlib import Path
prefix = 'round-native-cube-filtration'
old = 'round-native-cube-group'
modules = ['Hindman168/'+name+'.lean' for name in [
'NativeRationalCubeInclusion','NativeCubeAmbientLayers','NativeCubeAmbientRationality',
'NativeCubeInclusionRationality','NativeCubeInternalFiltration','NativeConjugateSubgroupFiltration',
'NativeFiniteProductDiagonalLattice','NativeResidueCubeData']]
components = [
'Proved actual native cube subgroup inclusion smoothness, its exact differential, exponential compatibility and adjoint intertwining. No supplied bracket compatibility is used.',
'Constructed every ambient cube layer as the actual full-array Lie embedding image. Proved antitonicity, initial equality, exact zero-layer model, actual bracket closure, termination and rationality for the specified product lattice.',
'Proved actual internal rational-log-span membership iff its inclusion lies in the ambient product-lattice rational span, using positive powers and actual exponential compatibility. Derived the FULL native cube rational Lie filtration with internal initial layers top and ORIGINAL degree and step bounds.',
'Transported the SAME possibly proper final subgroup filtration to rationally conjugated original native data, preserving every Lie and group layer exactly. The residue is only ambient-rational and need not lie in the subgroup.',
'Constructed the actual finite-product diagonal and proved product of conjugated lattices equals diagonal conjugation of the specified product lattice.',
'Constructed full native rational-residue cube data and rational filtration. Its group is the SAME original cube group, its lattice is EXACTLY the diagonal-conjugated original product lattice intersected with that group, and all internal Lie layers and the paper upper-face group identification are preserved.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
'Original q=0 weak probability limit and all-continuous tests, SAME-filtration actual native cube group, '
'EXACT paper upper-face identification, compact actual lattice quotient, FULL internal rational cube '
'filtration and rational-residue cube data preserving original step s and degree are proved. Remaining: '
'actual residue cube orbit maps/Haar images; face-character coefficient isolation and original source '
'adaptation; simultaneous local cube laws through ORIGINAL s+1 with length before locality; projected '
'face invariance/full support, joint lifts/full Alignment; separate arbitrary-input GTZ interval Gowers '
'LINEAR nilsequence inverse; final positive distinct rapidly separated SAME-color ALL nonempty FS AND FP. '
'No source/Haar/inverse oracle or new axiom introduced. Author checks are not independent kernel replay '
'or external peer review. Public repository/PR/prize milestone not reached.')
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
Pinned OpenAI section 7, actual cube filtration and rational residue lattice.

The actual inclusion of the exponential cube subgroup is a smooth group
homomorphism. Its differential is precisely the Lie-model subtype inclusion.
Exponential compatibility and adjoint intertwining are deduced from this
smooth homomorphism, rather than assumed as abstract filtration hypotheses.
The explicit local model topology is the topology of the existing norm;
it resolves an elaboration ambiguity without changing a space or structure.

The full pointwise Lie array embedding permits all upperFaceLieLayer levels
to be mapped into the actual ambient product Lie algebra. Layer zero equals
the model of the existing cube subgroup. Antitonicity, bracket closure and
termination come from the already proved SAME final filtration layers. Each
ambient layer is spanned by vectors in the actual specified product-lattice
rational log span, using the earlier coordinatewise rational spanning proof.

Internal layers are comaps along the actual model inclusion. Both initial
layers are all of the internal model, including a proper or trivial original
subgroup. Internal bracket closure uses the actual differential identity.
Rationality is not inferred merely from a real embedding: positive-power
characterizations and exponential compatibility prove the exact equivalence
of internal rational membership and ambient rational membership. The lattice
is the ACTUAL comap of product Gamma. Rational real span transport then
proves every internal layer rational. Degree ell and original step s persist.

For a rational ambient residue rho, the previously proved rational conjugate
log-span identity transports the original subgroup filtration to original
native data with lattice rho Gamma rho^-1. Every Lie layer and every group
layer remains literally unchanged. No membership of rho in the final H is
assumed. Taking the cube of this data therefore retains the SAME cube group
and ALL internal layers. The recursive diagonal in the genuine product has
coordinate rho at every vertex. Coordinatewise subgroup membership proves
that product(rho Gamma rho^-1) equals diag(rho) product(Gamma) diag(rho)^-1.
Thus the residue cube lattice is EXACTLY the required conjugated product
lattice intersection. This does not wrongly conjugate within the cube.
Compactness, discreteness, compatible metric and full rational filtration
are supplied by the already proved cube construction applied to these data.
The exact original paper upper-face group identification is retained.

This does not yet prove local cube laws, source adaptation, face-character
coefficient isolation, or orbit Haar support/invariance. No group or measure
oracle was added. The complete StrongConjecture is still unproved, with
Alignment, the arbitrary-input GTZ inverse, and the final same-color FS/FP
argument outstanding. No unavoidable obstruction has been established.
These author checks are not independent kernel replay or external review.
''', encoding='utf-8')
print(prefix)
