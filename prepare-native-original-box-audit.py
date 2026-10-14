from pathlib import Path
import ast

PREFIX='round-native-original-real-box'
OLD='round-native-rational-multiparameter-inverse'
MODULES=[
    'Hindman168/NativeOriginalPolynomialInverse.lean',
    'Hindman168/NativeOriginalBoundedCubeObstruction.lean',
    'Hindman168/NativeOriginalAffineCubeInput.lean',
    'Hindman168/NativeOriginalRealBoxObstruction.lean',
    'Hindman168/NativeOriginalFiniteRealBoxObstruction.lean',
]
COMPONENTS=[
    'UNCONDITIONAL general ORIGINAL native logarithmic-polynomial equal-cube inverse is now proved for every actual step bound, ordinary degree and finite variables. The actual rational stretched filtration at max(degree,1) supplies true weights. Original log identity supplies actual quotient orbit. Both COMPLETE raw output tables use ORIGINAL ordinary degree, original nonzero horizontal/grid/norm character and canonical native Haar. The stretched filtration degree is not silently substituted for the original binomial table.',
    'Arbitrary prescribed bounded complex Lipschitz observables are normalized BEFORE all sources and lengths against the SAME canonical native Haar probability. Actual Option-parameter specialization and literal affine source substitution produce the genuine translated-cube binomial input for every native step bound. All original source/log/orbit/mean/projection identities are proved; no translated-cube character-production or inverse premise remains.',
    'The corrected real-box finite obstruction is now proved for arbitrary native step bound, ordinary degree and finite spatial dimension. Exact retained corrected cube tiling, denominator clearing and ORIGINAL translation/location coefficient estimates are instantiated by the newly proved actual cube input. Original boxes/parameters/observables and raw polynomial coefficients vary after the fixed finite original character list, accuracy budget and length threshold. Every selected character is actual nonzero horizontal lattice character. ALL positive original spatial monomial rows at scale Z are retained.',
    'One SAME real-box accuracy budget and threshold now work across EVERY fixed finite list of actual native nilmanifolds, including empty lists. Genuine finite sums of positive bounds are chosen before all raw sources/samples/observables. No equidistribution inverse/production premise remains in the fixed-family box theorem. This closes the source quantitative Leibman box consequence in its fixed-data formulation, not rough progression comparison, Gowers correlation inverse, cube/Alignment or final FS/FP goal.',
]
REMAINING=(
    'StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
    'Complete unconditional native rational-filtration inverse for every finite variable type and all '
    'positive original equal-cube lengths, general ordinary-degree original logarithmic-polynomial inverse, '
    'and corrected general real-box finite-character obstruction including fixed finite native families '
    'are now proved. Original nonzero horizontal/grid/norm characters, canonical Haar, and complete '
    'original coefficient tables are retained. Remaining: connect ACTUAL original full/progression '
    'bad samples to these uniform box characters, synthesize true native rough progression dimension '
    'descent/comparison, distinct interval Gowers correlation inverse, cube/Alignment and final '
    'positive distinct rapidly separated monochromatic FS/FP StrongConjecture. Fixed-data existential '
    'constants do not certify explicit delta-power laws. Only true positive exponential lattice powers '
    'are used. Author checking is not independent kernel replay or external peer review. '
    'The repaired source slab estimate is not an unavoidable obstruction. Public repository/PR/prize '
    'milestone has not been reached.'
)
source=Path(OLD+'-audit.py').read_text(encoding='utf-8')
lines=source.splitlines(keepends=True)
replacements=dict(PREFIX=PREFIX,OLD=OLD,MODULES=MODULES,COMPONENTS=COMPONENTS,REMAINING=REMAINING)
for node in reversed(ast.parse(source).body):
    if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name):
        if node.targets[0].id in replacements:
            name=node.targets[0].id
            lines[node.lineno-1:node.end_lineno]=[name+' = '+repr(replacements[name])+'\n']
source=''.join(lines).replace(
    'unconditional complete corrected native rational-filtration inverse for every finite variable type and positive original length; separate Gowers correlation inverse and final target remain open',
    'unconditional general original native logarithmic-polynomial and corrected real-box finite-family obstruction; rough progression comparison, Gowers correlation inverse and final target remain open')
Path(PREFIX+'-audit.py').write_text(source,encoding='utf-8')
Path(PREFIX+'-mathematical-review.txt').write_text('''JSP-000168 mathematical/application review, 2026-10-13

Classification: PROGRESS. General native original logarithmic-polynomial and
corrected real-box finite-list obstruction now proved. StrongConjecture remains
UNPROVED; this is author-side application review, not independent replay.

1. Genuine ordinary-degree input. For fixed ordinary d, e=max(d,1)>0.
The TRUE nativeOriginalRationalLieFiltration D e has degree s*e and genuine
rational/bracket/terminal properties. Raw scalar term degree<=d<=e gives
true stretched weighted membership. Zero ordinary degree and step bound zero
are not discarded. The unconditional finite-variable inverse produces the
actual original nonzero horizontal lattice character. ALL raw monomial rows
survive unchanged. Complete integer Stirling transfer at ORIGINAL d gives
ALL original binomial rows under one enlarged natural budget. This proof
does not rely on d<=s*e, which is false when s=0, or equality of different
binomial tables without justification. True ordinary projection degree<=d
is later used for the exact d-truncated binomial expansion.

2. Actual orbit and canonical Haar. The original all-real logarithm identity
and true exponential/log inverse imply actual quotient orbit equality on
every integer cube sample. No source equality is inferred from sampled coset
equality. Probability is the actual nativeNilmanifoldQuotientProbability D,
with the original metric/topology and quotient measurable instance. The
abelian Haar is not substituted. A discovered extra borel quotient instance
in generated initial drafts was removed before verification, avoiding a
different typing of the canonical measure.

3. Bounded complex observables. R=max(1,max(B,L))>0 is fixed before ALL raw
source/length/F. The proved normalization lemma gives original unit observable
R^-1*F, and actual finite mean/canonical integral real-scaling identity gives
the exact discrepancy norm R^-1 times original. Accuracy eta/R is positive.
The same original character/grid/norm/two tables result. No global spatial
Lipschitz assertion about Fourier families or group action is introduced.

4. Literal affine cube. True Option parameter specialization and affine
substitution b+v preserve original ordinary source degree. All-real log
identity is checked against actual Q, and original native discrepancy is
transported through exact integer/natural cube means. The original spatial
scalar projection equals the literal affine projection polynomial. Actual
degree<=d gives its genuine COMPLETE constant-plus-positive-binomial expansion.
The complete coefficient bounds use original N>0; no row is missing. The
two Finset presentations have explicitly proved extensional equality.

5. Corrected box transfer. Existing rough_native_real_box_horizontal_transfer
already proves real integer box tiling with boundary strips, true large cube
selection, factorial denominator clearing, integer translation and location
error. The NEW actual affine cube theorem supplies ALL its analytic production
premises. Fixed original grid.image of positive roughBinomialMultiplier is
finite; every member is NONZERO, horizontal and integral by proved positive
natural character scaling. ALL original positive spatial monomial coefficients
are bounded by A'*Z^-weight. Constants precede original box endpoints, Q,p,z,F
and original source coefficients. Empty dimensions and degree zero are covered.

6. Finite native lists. For each datum the true fixed character list and
positive A_i,Z_i>=1 precede raw data. R=1+sum(A_i+Z_i) is positive even for
an empty family and exceeds each A_i,Z_i. Same threshold R and accuracy R
work simultaneously, using Z>=R>=1 and positivity of Z^-weight. Dependent
model/group types and SAME original canonical Haar are retained per datum;
no invalid equality between different quotient records is asserted.

7. Scope and next actual application. This closes the pinned Section 6
quantitative Leibman equal-cube/box-consequence input in its fixed-data
existential formulation. It does not prove the paper rough progression
comparison yet: actual original bad pair may yield full-box OR residue-box
Haar discrepancy, and the residue sample must be reparametrized with the
original polynomial, scale and affine coefficients retained. Finite original
character thinning then needs true raw coefficient inputs to existing smaller
dimension descent and termination. Separate interval GTZ Gowers correlation
inverse, full cube/Alignment and final monochromatic FS/FP remain open.
Explicit delta-power complexity is not certified. Source slab arithmetic and
all six pinned OpenAI sections are rechecked; repaired bound is not terminal
obstruction. Old proof hashes/axioms unchanged; standard axioms only. Public
repository/PR/prize user milestone has not been reached.
''',encoding='utf-8')
print(PREFIX)
