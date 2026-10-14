from pathlib import Path
import ast

PREFIX='round-native-actual-bad-characters'
OLD='round-native-original-real-box'
MODULES=[
 'Hindman168/RoughSpatialAffineSubstitution.lean',
 'Hindman168/RoughResidueBoxNormalization.lean',
 'Hindman168/NativeOriginalResidueBoxObstruction.lean',
 'Hindman168/NativeOriginalBadPairCharacters.lean',
 'Hindman168/RoughNativeRealBadIndexComplex.lean',
 'Hindman168/NativeOriginalRealBadPairCharacters.lean',
 'Hindman168/RoughOriginalBadPairScaleThresholds.lean',
 'Hindman168/NativeOriginalAsymptoticBadPairCharacters.lean',
]
COMPONENTS=[
 'ACTUAL original residue classes reduce modulo the positive step and have EXACT normalized complex mean on the genuine quotient integer box. TRUE quotient-box length/location geometry and LITERAL Option-parameter-preserving spatial affine source/evaluation/scalar-projection identities are proved. No equality of vector/source polynomials is inferred from sampled quotient equality.',
 'ACTUAL original residue-box Haar discrepancy now PRODUCES one TRUE nonzero original horizontal lattice character in a fixed finite ORIGINAL list, plus ALL positive original spatial affine coefficient rows. It is instantiated by the UNCONDITIONAL general corrected native box theorem. The list, accuracy constant and quotient-scale threshold precede every original step/residue/source/box/parameter/observable. Exact reduced residues are retained as natural basepoints less than the original step.',
 'Both ACTUAL original full-box and residue-box Haar branches of a complex bad pair are now closed to one fixed finite ORIGINAL character list and ONE coefficient constant. The SAME character controls ALL positive affine rows; output step is literally 1 OR original t, and all natural affine basepoints are bounded by that step. Real bad pairs embed into the complex statement with EXACT discrepancy and unchanged Lipschitz/norm/geometry/sampling data. No inverse or character-production premise remains.',
 'TRUE PowerDominates and actual eventually-positive scales supply ONE source-independent asymptotic threshold for ALL original dyadic steps at once. Original finite character list and coefficient budget are fixed BEFORE ALL scale indices/raw Q/p/steps/boxes/observables. native_original_asymptotic_bad_pair_characters derives ALL positive original affine coefficient rows from ACTUAL RoughNativeBadIndex, with no analytic production premise. Common-character parameter thinning and full native dimension-descent comparison remain to be assembled.',
]
REMAINING=(
 'StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Complete '
 'unconditional native rational-filtration inverse, general original ordinary-degree inverse, corrected '
 'native real-box finite-family obstruction, and ACTUAL original full/residue bad-pair character production '
 'with ONE fixed original finite character list and ALL positive affine coefficient rows are now proved. '
 'True original residue mean/geometry/source identities, exact real-to-complex discrepancy and genuine '
 'PowerDominates uniform dyadic threshold are supplied. Remaining: common original character on a '
 'smooth parameter subprogression with literal reparametrized source/full rows, simultaneous finite '
 'kernel geometry/budgets, true all-native dimension induction and rough progression comparison, '
 'distinct interval Gowers correlation inverse, cube/Alignment and final positive distinct rapidly '
 'separated monochromatic FS/FP StrongConjecture. Fixed-data constants do not certify explicit '
 'delta-power laws. Author checking is not independent replay/external peer review. Repaired source '
 'slab estimate is not an unavoidable obstruction. Public repository/PR/prize milestone not reached.'
)
source=Path(OLD+'-audit.py').read_text(encoding='utf-8')
lines=source.splitlines(keepends=True)
replacements=dict(PREFIX=PREFIX,OLD=OLD,MODULES=MODULES,COMPONENTS=COMPONENTS,REMAINING=REMAINING)
for node in reversed(ast.parse(source).body):
 if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name):
  name=node.targets[0].id
  if name in replacements:
   lines[node.lineno-1:node.end_lineno]=[name+' = '+repr(replacements[name])+'\n']
source=''.join(lines).replace(
 'unconditional general original native logarithmic-polynomial and corrected real-box finite-family obstruction; rough progression comparison, Gowers correlation inverse and final target remain open',
 'actual original full/residue bad-pair character production and complete affine coefficient rows under one fixed finite list and uniform dyadic threshold; full rough comparison and final target remain open')
Path(PREFIX+'-audit.py').write_text(source,encoding='utf-8')
Path(PREFIX+'-mathematical-review.txt').write_text('''JSP-000168 mathematical/application review, 2026-10-13

Classification: PROGRESS. Actual original bad-pair finite character production
now proved. Full rough progression comparison and StrongConjecture UNPROVED.
Author-side proof application review and Lean checks, not independent replay.

1. Literal spatial source. Option parameter none is fixed by scalar affine
substitution none -> 0+1*none; each spatial some j -> b_j+k_j*some j. RingHom
extensionality on constants/variables proves exact commutation with parameter
specialization. Original vector projection and eval identities follow from
actual termwise source construction. No coefficient-size premise is imposed,
and no sampled coset equality is promoted to vector/source equality.

2. Original residue sample. Every arbitrary integer residue reduces modulo
positive t, with exact alignmentBoxClass equality by modular arithmetic. Its
actual normalized complex mean equals the normalized quotient integer-box
mean by the registered division identity. Original integer endpoints are
actual alignmentRetainedEndpoints. Existing exact endpoint error gives true
side length >=(c/2)*(Z/t) and original location <=(C+1)*(Z/t), under t<=Z and
t<=(c/2)*Z. Empty dimensions are included; means remain exact even if a sample
set is empty. Positive bad input itself prevents empty-sample problems where
nonemptiness is required by the original bad-pair definition.

3. Genuine original residue character. The unconditional corrected real-box
theorem at fixed c/2,C+1,B,L,eta fixes S,A,Z0 BEFORE t,Z,lo,hi,v,Q,p,z,F.
Natural b=(v mod t).toNat satisfies b<t and integer b=v mod t. The actual
joint source r is spatial-affine-substituted p with unchanged parameter,
true degree<=d and ALL-real original logarithm identity. Exact original
quotient mean and SAME canonical native Haar yield the true transformed
discrepancy. The produced ORIGINAL nonzero horizontal lattice character is
in S and ALL positive raw affine original spatial coefficients obey
A*(t/Z)^weight. This uses inverse(Z/t)=t/Z exactly; no missing row or
source-dependent finite list replaces the actual output.

4. Full and residue branches. Original actual complex bad pair has true
eta/2 Haar discrepancy on at least one actual original sample. BOTH branches
are retained. The fixed union Sf union Sr and max Af Ar are chosen before
ALL raw data. Full branch uses literal affine step 1 and basepoint 0; the
zero/one substitution is exactly the identity RingHom. Residue branch uses
actual t and b<t. Both yield SAME character for EVERY positive multiindex,
affine step exactly 1 or original t, and bounded natural basepoints. Increasing
the common budget uses true nonnegative original scale powers.

5. Real bad input. Complex embedding of real observable is isometric and
preserves its Lipschitz/norm bounds. FiniteMass.complexExpectation of ofReal f
is EXACT ofReal original real expectation by finite sum arithmetic. Norm of
the original expectation difference is EXACT absolute real difference. Thus
real RoughNativeBadIndex gives complex bad input at SAME eta, not eta/2. The
finite character list and ALL affine rows survive without any extra premise.

6. Uniform asymptotic threshold. PowerDominates means all fixed powers are
little-o(Z); it does not assert desired sampling errors. Eventually 1<=Scale
and 0<=Z are actual scale hypotheses. A fixed R=2*Z0+4/c+2 gives R*Scale<=Z
eventually. For EVERY t in [Scale,2Scale), this proves t>0,Z>=Z0,Z/t>=Z0,
t<=Z and t<=(c/2)*Z. Hence native_original_asymptotic_bad_pair_characters
chooses S,A BEFORE all scale indices and eventually produces ALL original
affine rows from every ACTUAL original real bad input at every dyadic step.
No rough coprimality is needed at this stage; it is retained for later
interpolation/dimension descent. No production/inverse/oracle premise remains.

7. Exact scope and remaining composition. Final output is an actual ORIGINAL
finite horizontal-character packet for each bad input. It does not yet choose
ONE common character over a smooth exceptional PARAMETER progression. Literal
parameter affine reparametrization must preserve original source/degree/log,
ALL coefficient rows, original bad samples and genuine smoothness/coprimality.
Finite geometry/canonical kernel budgets must precede source/w, then genuine
all-native strong finrank induction closes rough comparison. GTZ correlation
inverse, cube/Alignment and final FS/FP remain open. Fixed-data constants are
not explicit delta-power laws. Old registered hashes/axioms, actual pins/six
OpenAI proof sections and exact slab certificate are rechecked. Repaired slab
estimate is not terminal obstruction. Standard axioms only; author checking is
not independent replay/external review. Public repo/PR/prize not reached.
''',encoding='utf-8')
print(PREFIX)
