from pathlib import Path
prefix = 'round-native-cube-group'
old = 'round-native-cube-lie'
modules = ['Hindman168/'+name+'.lean' for name in [
'NativeRationalCubeSubgroup','NativeRationalCubeLatticeGeometry','NativeRationalCubeMetric',
'NativeRationalCubeData','NativeFiniteProductCoordinateHom','NativeRationalCubeFaceInclusion',
'UpperFaceLieVertexDetection','UpperFaceGroupVertexElimination','NativeRationalCubeGroupIdentification']]
components = [
'Constructed the actual exponential subgroup of the embedded SAME-filtration cube Lie algebra in the original finite product. Membership is equivalent to an actual Lie-cube witness with all original exponential vertex coordinates.',
'Proved discreteness, compactness and metrizability for the actual intersection of the specified product lattice with this exponential subgroup. No normality or assumed compactness of restricted lattices is used.',
'Constructed a compatible quotient metric and full native cube nilmanifold data with the ACTUAL group/lattice and ORIGINAL step bound s, including zero-dimensional and trivial subgroup cases.',
'Constructed actual injective finite-product vertex group homomorphisms. Every original upper-face generator in its SAME final filtration layer belongs to the exponential cube image, proving the forward subgroup inclusion.',
'Proved triangular Lie vertex detection from unique face coefficients and a generic group vertex-elimination theorem from actual ordered faces. Native exponential injectivity discharges every triangular layer premise.',
'Proved EXACT equality of the exponential cube subgroup vertex image with the paper upperFaceCubeGroup of the SAME final filtration, in BOTH directions. No exponential-generation, coordinate-recovery or group-identification oracle is assumed.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
'Original q=0 weak probability limit and all-continuous tests, SAME-filtration cube Lie algebra, '
'actual native exponential cube group and EXACT paper upper-face identification, compact actual '
'lattice quotient and native cube nilmanifold data preserving original step s are proved. Remaining: '
'full rational cube filtration on the native subgroup, rational conjugated residue cube orbit data, '
'face-character coefficient isolation and original source adaptation; simultaneous local cube laws '
' through ORIGINAL s+1 with length before locality; projected face invariance/full support, joint '
'lifts/full Alignment; separate arbitrary-input GTZ interval Gowers LINEAR nilsequence inverse; '
'final positive distinct rapidly separated SAME-color ALL nonempty FS AND FP. No source/Haar/inverse '
'oracle or new axiom introduced. Author checks are not independent kernel replay or external peer '
'review. Public repository/PR/prize milestone not reached.')
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
Path(prefix+'-mathematical-review.txt').write_text("Author mathematical review, 2026-10-14.\nPinned OpenAI 07_cube_limits.tex, upper-face coordinates and rational cube\ngroup construction. This round connects the previously proved Lie algebra\nto the ACTUAL group and actual original lattice quotient.\n\nThe native subgroup is the exponential image of the embedding's Lie range.\nThe original proven native Lie-subalgebra theorem supplies group closure.\nIts membership theorem is an existential witness in the original cube Lie\nalgebra, with exact original exponential values at every vertex. Coordinate\ninjectivity proves the reverse implication; no surrogate group is used.\n\nThe actual product-lattice rationality from the preceding round discharges\nthe hypothesis of nativeRationalLieLattice_quotient_compact. The lattice is\nexactly product Gamma comapped along the ACTUAL subgroup inclusion. Its\ndiscreteness and compact quotient are derived. Gamma need not be normal.\nThe metric has exactly the natural coset topology, and the quotient map is\nopen. Native data uses genuine subgroup Lie structures and retains ORIGINAL\nstep bound s by finite product and subgroup nilpotency-class bounds.\n\nFor a face A and g in H_cardA, original log(g) lies in the corresponding\nLie layer. Its single-face Lie vector exponentiates exactly to the original\nupperFaceArray A g; the zero coordinates exponentiate to identity. Thus\nevery generator of the paper group lies in the native vertex image.\n\nThe reverse inclusion is not inferred from that one-sided result. First,\nif a Lie cube vanishes on every proper subvertex of V, triangular powerset\nrecovery makes all proper face coefficients zero. Its value at V is exactly\nthe V coefficient, which lies in H_cardV's Lie layer. Original exponential\ninjectivity therefore implies the analogous group-layer detection property.\n\nA separate generic elimination theorem removes vertices in the actual\norderedCubeFaces order. At the current face D every proper subset has\nalready been removed, so the detected z(D) lies in H_cardD. Multiply by the\ninverse of its D-face. Closure keeps the residual in the native image.\nUpward closure of the remaining face list ensures already removed vertices\nremain identity. The empty suffix is the identity array. All factors are\nactual paper generators, proving the reverse inclusion and EXACT equality.\nThe generic triangular premises are completely discharged in the final\nnative theorem; they are not an oracle or final assumption.\n\nThe constructions include d=0 through the existing actual enumeration of\n2^d vertices. The final filtration can be proper or trivial. No extraction,\nsource replacement, lower-central substitution or reduced nilpotency bound.\n\nThis is NOT yet the simultaneous cube law: native rational filtration on\nthe cube subgroup, conjugated rational residue orbit data, original source\nadaptation, horizontal face restrictions/coefficient isolation and analytic\nlocal cube laws through original s+1 still remain. Projected face invariance/\nfull support, joint lifts/full Alignment, separate GTZ inverse and final\nSAME-color ALL nonempty FS/FP with positivity, distinctness and rapid\nseparation also remain. No unavoidable obstruction established.\nAuthor checks are not independent kernel replay or external peer review.\n", encoding='utf-8')
print(prefix)
