from pathlib import Path
prefix='round-native-cube-box-haar'
old='round-native-cube-source'
modules=['Hindman168/'+n+'.lean' for n in ['RoughVectorSpatialLift','CubeSpatialTopCoefficient','NativeResidueCubeSpatialSource','NativeResidueCubeFiniteEscape','NativeResidueCubeRealBoxHaar','NativeResidueCubeProgressionHaar','NativeResidueCubeSimultaneousHaar']]
components=[
'Constructed a true spatial lift of every original polynomial variable, with a new unused Option parameter. Proved exact evaluation, degree, projection and injective coefficient identities; the original cube base variable is never fixed.',
'Reindexed ALL cube variables to Fin(d+1), with base coordinate zero and increments at successors. Proved the isolated monomial retains degree j, and arbitrary translations plus uniform dilation t multiply its top coefficient by exactly t^j.',
'Constructed the actual residue-cube spatial source and a degree-ell polynomial representation. Proved its logarithm identity, exact original source at every vertex and the complete spatial projection/affine coefficient formulas.',
'Derived a single eventual threshold for every character in ANY fixed finite list of actual residue-cube horizontal functionals. At every fixed nonzero rational step, an original escaping coefficient defeats every fixed bound uniformly over all translations and the unused parameter.',
'Applied the PROVED quantitative real-box obstruction theorem to the ACTUAL degree-bounded cube source and excluded its finite character alternatives. This proves Haar convergence uniformly over real integer boxes of original-scale side lengths and bounded Lipschitz tests.',
'Applied the PROVED residue-box obstruction theorem and retained the exact original scale to obtain Haar convergence on every fixed-positive-modulus progression box, uniformly over integer endpoints, all residue vectors and bounded Lipschitz tests.',
'Combined the actual progression-box Haar laws for ALL cube dimensions 0 through ORIGINAL s+1 and every member of the SAME finite rational residue family into one eventual threshold. The original source, filtration, scale and subsequence are unchanged.'
]
remaining=('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
'Actual cube geometry, same-source adapted cube polynomial, top coefficient escape and its spatial/'
'fixed-progression transport are proved. The actual cube now has uniform real-box and fixed-modulus '
'progression-box Haar convergence, simultaneously through ORIGINAL s+1 and all fixed rational residues. '
'Remaining: transport these pure-source Haar laws to original ambient cube Haar images, insert the '
'original smooth factors and exact periodic residue factors, and prove the local alpha-down-to-zero '
'limit AFTER the length limit with its uniform versions; projected face invariance/full support, '
'joint lifts/full Alignment; separate arbitrary-input GTZ interval Gowers LINEAR nilsequence inverse; '
'final positive distinct rapidly separated SAME-color ALL nonempty FS AND FP. No source/Haar/'
'character/inverse oracle or new axiom introduced. Author checks are not independent kernel replay '
'or external peer review. Keep the user-requested GitHub repository PRIVATE. Public repository/'
'PR/prize milestone not reached.')
for source,target in [('verification-manifest.json',prefix+'-baseline.json'),('lakefile.toml',prefix+'-lakefile-before.toml')]:
    dest=Path(target)
    if dest.exists(): assert dest.read_bytes()==Path(source).read_bytes()
    else: dest.write_bytes(Path(source).read_bytes())
replacements={'PREFIX=':prefix,'OLD=':old,'BASELINE=':prefix+'-baseline.json','MODULES=':modules,'COMPONENTS=':components,'REMAINING=':remaining}
lines=[]
for line in Path(old+'-audit.py').read_text(encoding='utf-8').splitlines():
    key=next((k for k in replacements if line.startswith(k)),None)
    lines.append(key+repr(replacements[key]) if key else line)
source=('\n'.join(lines)+'\n').replace(old+'-lakefile-before.toml',prefix+'-lakefile-before.toml')
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
Path(prefix+'-mathematical-review.txt').write_text('''Author mathematical review, 2026-10-14.
Pinned OpenAI section 7: exclude cube horizontal obstructions and obtain box Haar laws.

The existing quantitative box interface reserves Option.none as a FIXED parameter.
In the cube polynomial Option.none was b0, which MUST be averaged. We do not
identify these meanings. roughVectorSpatialLift renames all original variables
into spatial variables, adding a new unused parameter. Exact evaluation and
spatial projection identities prove no original variable is lost. Injective
renaming preserves each desired coefficient. cubeSpatialVariableEquiv sends
original none to spatial 0 and original some k to spatial k.succ. The source
vertex formula is literally x(0)+sum present x(k.succ), independent of the new z.

The selected spatial monomial has exactly its original total degree j. The
previous round proved the ENTIRE horizontal projection has degree <=j. Therefore
rough_translation_top_coefficient applies to arbitrary translations, and the
proved uniform affine coefficient formula multiplies it by t^j. This step would
be invalid using only a one-coefficient identity without the whole-degree bound.

For each genuine horizontal functional in a fixed finite set, actual coefficient
escape selects j>=1, j<=ell and a face A. Apply escape to the nonzero rational
multiple t^j. The exact affine identity removes dependence on every translation
and unused parameter. Finite intersection produces one index threshold before
all characters, translations and parameters. Empty finite sets are included.
No horizontal-character production or compactness oracle is supplied.

For real boxes, native_original_real_box_finite_obstruction is a proved theorem
on the actual residue cube data. The spatial source has ordinary degree<=ell and
an exact logarithm representation, so all its hypotheses are discharged. Haar
failure yields a character in its fixed finite list and coefficient <=K*L^(-j).
Eventually L>0. Multiplying by L^j gives <=K, contradicting uniform escape. The
box endpoints and every bounded Lipschitz test are quantified AFTER the threshold.

For integer progression boxes, native_original_residue_box_obstruction supplies
bounds after the true fixed modulus and residue substitution. Its size hypotheses
Z0<=L/t, t<=L and t<=(c/2)*L follow from original L tending to infinity, with
positive fixed integer t. Multiplying the bound K*(t/L)^j by L^j gives K*t^j.
Since t>=1 and j<=ell, this is <=K*t^ell; uniform escape contradicts that common
bound. Arbitrary signed integer endpoints and all residue vectors are allowed.
The modulus t is fixed before the limit, as required by the paper.

Finally use finite universal quantification over q:Fin(s+2) and r:Fin(M). This
is exactly q=0,...,ORIGINAL s+1 and the SAME given rational residue family. The
canonical vertex enumeration has 2^q vertices. All dimensions share the original
source p, scale L, filtration F and subsequence. No dimension-specific descent
or new subsequence is chosen. The common threshold also precedes all admissible
boxes, residue vectors and tests. Trivial/zero-dimensional cases are retained.

LIMIT: these are genuine cube Haar laws for the irrational adapted source Q_L,
before inserting smooth h_L and periodic gamma_L from original factorization.
They are NOT yet the full original-source local cube law. One must transport
through actual orbit/Haar-image maps, control all vertex smooth multipliers
uniformly near beta as alpha shrinks, use the exact common right residue, and
prove length goes to infinity BEFORE alpha goes to zero. Uniformity over bounded
tests/boxes must be retained. Existing point-law results are not replaced.
Projected face invariance, joint lifts/Alignment, separate GTZ arbitrary-input
inverse and final same-color FS/FP still remain. StrongConjecture UNPROVED.
Goal ACTIVE; no unavoidable obstruction established. No additional axioms or
source/Haar/character/inverse oracles. Author audit is not independent kernel
replay or external peer review. Keep the user-requested repository PRIVATE.
''',encoding='utf-8')
print(prefix)
