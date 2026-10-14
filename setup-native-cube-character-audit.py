from pathlib import Path
prefix = 'round-native-cube-character'
old = 'round-native-cube-haar'
modules = ['Hindman168/'+name+'.lean' for name in [
'UpperFaceCharacterBracket','UpperFaceCharacterMaximal','NativeCubeArrayFunctional',
'NativeCubeHorizontalArray','NativeCubeFaceLevelCharacter','NativeResidueCubeLevelCharacter',
'NativeResidueCubeFaceEscape']]
components = [
'Proved actual finite-face splitting and bracket annihilation for a cube functional, including empty faces. Proved a nonzero cube functional is detected by a spanning face and selected the greatest surviving level across ALL faces of the SAME filtration.',
'Constructed the actual cube Lie-model surjection and a full-array extension of any native cube functional using a proved finite-dimensional retraction. Proved exact restriction agreement, nontriviality and compatibility with the actual native adjoint bracket.',
'Derived bracket annihilation and rationality of the array functional from a genuine horizontal functional on the ACTUAL cube nilmanifold. Rationality uses actual internal/product lattice rational-log-span compatibility and lattice integrality, not a rationality oracle.',
'Proved every genuine horizontal cube obstruction yields a nonzero ORIGINAL rational level character at some greatest j between 1 and the original degree, on a face of cardinality at most j. All higher face restrictions vanish; both next-layer and mixed-bracket annihilation are proved.',
'Transported the result from rationally conjugated original data to the ACTUAL residue cube and ORIGINAL rational form. The residue is only ambient-rational; no membership in H or the cube is required.',
'Connected the selected residue cube face character to SAME-original-source sequential irrationality. Its Taylor face value divided by (j-card(face))! escapes every fixed nonzero rational multiple at scale L^j. This proves scalar escape, not yet polynomial coefficient identification.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
'Original q=0 weak probability limit, SAME-filtration actual cube group, full rational filtration, '
'rational-residue orbit/Haar probability with exact full support and cube invariance, and ACTUAL '
'horizontal cube obstruction to ORIGINAL maximal rational face-level character with Taylor scalar '
'escape are proved. Remaining: identify the isolated actual cube polynomial coefficient without '
'cancellation and prove original source cube adaptation; simultaneous local cube laws through '
'ORIGINAL s+1 with length before locality; projected face invariance/full support, joint lifts/full '
'Alignment; separate arbitrary-input GTZ interval Gowers LINEAR nilsequence inverse; final positive '
'distinct rapidly separated SAME-color ALL nonempty FS AND FP. No source/Haar/character/inverse '
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
Path(prefix+'-mathematical-review.txt').write_text('''Author mathematical review, 2026-10-14.
Pinned OpenAI section 7, horizontal cube obstruction and maximal face level.

For a face D with card(D)<=a+b, choose a subset A of cardinality
min(a,card(D)) and B=D minus A. Their union is D and card(A)<=a, card(B)<=b.
Antitonicity puts the face arrays of x in F_a and y in F_b into the SAME
cube Lie layer zero. The actual face-bracket union identity then proves
annihilation of the D-face of [x,y] for any horizontal array functional.
Empty faces and a or b zero are included; the final character only needs
positive a,b. No invalid nonempty/disjoint-face requirement is introduced.

Nontriviality on the span of actual face arrays implies a nonzero face
generator. Its first allowed positive level is max(1,card(D)); F0=F1 handles
the empty face. Termination forces this level <=ell. The finite maximum is
taken over ALL levels and ALL faces, not a single arbitrarily selected face.
Every higher level and every face of cardinality <= that level then vanish,
including levels beyond ell by actual terminal zero and antitonicity.

The actual cube Lie embedding is surjective onto the internal model by its
range definition. A constructed finite-dimensional continuous linear
retraction extends any internal functional to the full array space. Its
agreement on actual cube arrays is proved using the true embedding and
retraction identity. Nontriviality follows from surjectivity, not an assumed
coordinate extension. Actual Lie-map bracket compatibility plus the proved
smooth subgroup inclusion differential identifies the internal bracket.

A horizontal functional of the actual cube data kills its actual first
commutator model. The preceding bracket identity therefore makes its array
extension kill all brackets of cube-layer-zero vectors. Coordinatewise
original rationality gives rationality in the specified product lattice;
the proved internal inclusion iff gives internal lattice rationality.
Integrality of the horizontal functional on the actual internal lattice
then implies rational values. This discharges genuine geometric rationality,
without assuming an arbitrary array functional has rational coefficients.

The selected face restriction is an ambient linear functional on ORIGINAL
D.E. Its nonzero value is witnessed on F_j; maximality kills F_(j+1);
finite face splitting and horizontal bracket annihilation kill every
[F_a,F_b] with positive a+b=j. The rational-array argument proves rationality
on F_j intersect ORIGINAL Gamma's rational log span. Hence all fields of
NativeSubgroupRationalLevelCharacter are proved, not supplied.

Apply this theorem to nativeConjugateNilmanifoldData D rho and its SAME-layer
filtration. The actual resulting cube is the previously constructed residue
cube. Rational conjugation preserves the original Q-log-span, so the level
character transports back to ORIGINAL D and F, retaining all tail vanishing.
rho is only ambient rational and need not be in H. Degree ell and step s
remain the original bounds; no refactorization for each dimension occurs.

Finally SAME-source NativeSubgroupSequentialIrrational applies to every
nonzero rational multiple of this character. Using q/(j-card(D))! proves
escape of the exact anticipated Taylor scalar for every fixed nonzero q.
This step DOES NOT claim that scalar is already an actual cube polynomial
coefficient: Boolean/binomial expansion, no-cancellation coefficient
identification and source cube adaptation remain to be formalized.

The local cube laws, projected face symmetries, joint lifts/Alignment, GTZ
arbitrary-input inverse and final FS/FP theorem remain outstanding.
StrongConjecture remains UNPROVED; no unavoidable obstruction established.
Author checks are not independent kernel replay or external peer review.
''', encoding='utf-8')
print(prefix)
