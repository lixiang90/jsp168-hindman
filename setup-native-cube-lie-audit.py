from pathlib import Path
prefix = 'round-native-cube-lie'
old = 'round-native-point-probability'
modules = ['Hindman168/'+name+'.lean' for name in [
'PointwiseLieAlgebra','UpperFaceLieArray','UpperFaceLieFiltration','UpperFaceLieCoordinates',
'UpperFaceLieRestrictedSpan','NativeRationalCubeLieLayers','NativeRationalCubeLieEmbedding',
'NativeFiniteProductRationalSpan','NativeRationalCubeLieImage']]
components = [
'Constructed exact pointwise Lie arrays and upper-face Lie homomorphisms, including the empty face. Proved bracket(face D x,face E y)=face(D union E)[x,y] and individual injectivity.',
'Constructed the paper cube Lie layers using max(i,card D) in the SAME arbitrary adapted filtration. Proved antitonicity, initial layer equality, bracket i+j and terminal vanishing, without substituting lower-central layers.',
'Proved Boolean upper-face coordinate existence and uniqueness by actual powerset sums and triangular recovery. Each filtered array has unique coefficients in its specified max(i,card D) layers; no direct-sum independence oracle is assumed.',
'Layerwise restricted spanning proves coordinatewise rational vectors span every cube Lie layer. Applied to the ORIGINAL final rational subgroup filtration, with its actual native bracket.',
'Constructed an injective Lie homomorphism into the genuine native finite product algebra and proved exact original exponential vertex coordinates. An actual enumeration exists for all 2^d vertices, including d=0.',
'Proved coordinatewise rational logarithms are rational for the ACTUAL original product lattice by constructing common positive powers. Combined this with restricted spanning to prove the embedded cube Lie algebra range is nativeLatticeRationalSubspace for that specified product lattice.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
'Original q=0 probability weak limit and all-continuous tests are proved. SAME-filtration cube Lie '
'layers, unique linear face coordinates, genuine native product embedding and its ACTUAL lattice '
'rationality are now proved. Remaining: exponential cube subgroup identification, compact quotient '
'and complete native cube data/filtration; face-character coefficient isolation; simultaneous local '
'cube laws through ORIGINAL s+1 with length before locality; projected face invariance/full support, '
'joint lifts/full Alignment; separate arbitrary-input GTZ interval Gowers LINEAR nilsequence inverse; '
'final positive distinct rapidly separated SAME-color ALL nonempty FS AND FP. No source/Haar/inverse '
'oracle or new axiom introduced. Author checks are not independent kernel replay or external peer '
'review. No public repository/PR/prize milestone yet.')
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
Path(prefix+'-mathematical-review.txt').write_text('Author mathematical review, 2026-10-14.\nPinned OpenAI 07_cube_limits.tex, upper-face coordinates and explicit\ncube-group-filtration. This round proves the Lie algebra and its genuine\nnative product-lattice rationality, not the complete local cube law.\n\nArrays are actual vertex functions, with explicitly supplied local pointwise\nLie structures. No global instance changes or native bracket replacements.\nThe face homomorphism is x on vertices containing D and zero elsewhere.\nThe exact bracket identity uses D union E and covers the empty face.\n\nLayer i is the REAL span of faces with x in F(max(i,card D)). Its bracket\nis closed at i+j because max(i,card D)+max(j,card E) is at least i+j and\nat least card(D union E). The two-sided span induction uses actual Lie\nbilinearity. Initial equality uses F0=F1, with card D=0 handled separately.\nTerminal vanishing follows antitonicity from F(ell+1)=0. The SAME final\nfiltration is used; F0 is allowed to be a proper original Lie subspace.\n\nThe value of a face sum at V is exactly the sum over powerset V. Strong\ninduction over proper subsets recovers each coefficient, proving injectivity.\nSpan induction constructs all coefficients with their stated layer bounds;\ntherefore existence and uniqueness are proved, not installed as structure\nfields. This is LINEAR Lie-array coordinates, not yet the ordered nonlinear\ngroup-coordinate diffeomorphism.\n\nRestricted spanning needs only P(0) and original layer spanning by P-vectors.\nEach single-face vector is coordinatewise P; its span gives the whole cube\nlayer. Native application takes P equal to membership in the actual original\nlattice rational logarithm span. This alone is not assumed to imply actual\nproduct-lattice rationality; a separate theorem proves that step.\n\nThe native embedding is the actual finite product Lie map of vertex\nevaluations restricted to the cube algebra. Surjectivity of the finite\nvertex enumeration proves injectivity. The original finite product\nexponential theorem identifies every coordinate with the original\nexponential. The enumeration has 2^d vertices, so d=0 remains a nonempty\nsingle-coordinate product.\n\nFor actual product rationality, recursively combine positive exponents a,b\nas a*b. Membership of each component follows from its original lattice\nmembership after raising to b or a, respectively. No normal lattice is\nassumed. The rational-power characterization then gives actual membership\nin the product rational log span. Applying this to restricted generators\nand using linear span induction proves nativeLatticeRationalSubspace for\nthe embedded cube algebra range and the SPECIFIED product lattice.\n\nRemaining are the exponential subgroup / upper-face generated-group\nidentification, compact lattice quotient and full native cube datum, actual\nface-character coefficient isolation, simultaneous source cube laws through\noriginal s+1, face invariance/full support, joint lifts/full Alignment,\nseparate GTZ inverse and the full positive distinct rapidly separated\nSAME-color ALL nonempty FS and FP conclusion. No unavoidable obstruction.\nAuthor checks are not independent kernel replay or external peer review.\n', encoding='utf-8')
print(prefix)
