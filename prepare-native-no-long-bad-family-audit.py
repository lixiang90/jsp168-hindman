from pathlib import Path
import ast

PREFIX='round-native-no-long-bad-family'
OLD='round-native-actual-bad-characters'
MODULES=[
 'Hindman168/RoughParameterAffineProjection.lean',
 'Hindman168/NativeOriginalCommonBadCharacter.lean',
 'Hindman168/NativeOriginalHorizontalKernelGeometry.lean',
 'Hindman168/NativeOriginalHorizontalKernelDescent.lean',
 'Hindman168/NativeOriginalActualHorizontalKernelDescent.lean',
 'Hindman168/NativeOriginalCommonBadFamily.lean',
 'Hindman168/NativeNoLongBadFamilyStatement.lean',
 'Hindman168/NativeNoLongBadFamilyInductionStep.lean',
 'Hindman168/NativeNoLongBadFamily.lean',
]
COMPONENTS=[
 'ACTUAL original bad parameter progression now yields ONE common original nonzero horizontal/integral character on a genuine smooth subprogression, with LITERAL raw parameter-affine source, true degree/all-real log, same original bad samples, scale and rough coprimality, and ALL positive original affine coefficient rows. Fixed finite character pool and natural source lengths precede raw inputs; empty character pools assert no fake geometry. Real-power paper growth supplies the actual asymptotic thresholds.',
 'TRUE original horizontal character alone now supplies rational full Lie-subalgebra geometry, genuine normalized rational pivot V, positive original lattice power K, and actual canonical finite kernel family with STRICT original finrank decrease. Original real bad samples produce actual complex observables/geometry/mean discrepancy and every affine row input to the existing normalized kernel descent. No supplied pivot/subgroup/period, scalar model, inverse or analytic production oracle remains.',
 'Finite budgets are now assembled across EVERY candidate in the ACTUAL original finite character pool and EVERY canonical child. A common positive child target length and common original coefficient-packet length are chosen by finite sums BEFORE raw sources/w. True child bad-family length restriction, finite intersection of eventual thresholds and common-character production close the original step using ONLY legitimate universal strictly smaller-native-finrank IH. Source coefficients, boxes, residues and tests remain arbitrary.',
 'UNCONDITIONAL NativeNoLongBadFamilyStatement D is now PROVED for EVERY legitimate actual native datum D by genuine strong NATURAL finrank induction and true dimension-zero base. For every fixed ordinary degree/spatial dimension/bounded geometry and original real-power growth sequence, ONE positive length is chosen and eventually NO actual original bad family of that length exists. All smaller-native premises are discharged. This closes the strengthened bad-progression comparison; original exceptional-proportion rough-step conclusion, separate Gowers correlation inverse and final FS/FP remain open.',
]
REMAINING=(
 'StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Complete '
 'unconditional native rational-filtration/ordinary-degree inverse, corrected real-box finite-family '
 'obstruction, actual bad-pair character production, genuine common smooth parameter-character/source/row '
 'transport and finite canonical kernel descent are proved. UNCONDITIONAL no-long-original-bad-family '
 'statement for EVERY actual native datum is proved by true strong natural finrank induction, with '
 'actual zero base and all finite original candidate/child budgets. Remaining: original exceptional '
 'proportion rough-step comparison (finite dense Szemeredi extraction, original residue-index interval, '
 'smooth step and literal joint source transport), separate arbitrary-input GTZ interval Gowers '
 'correlation inverse, cube/Alignment synthesis and final positive distinct rapidly separated '
 'monochromatic FS/FP StrongConjecture. Fixed-data constants do not certify explicit delta-power '
 'laws. Author checking is not independent replay/external review. Repaired source slab estimate '
 'is not unavoidable obstruction. Public repository/PR/prize milestone not reached.'
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
 'actual original full/residue bad-pair character production and complete affine coefficient rows under one fixed finite list and uniform dyadic threshold; full rough comparison and final target remain open',
 'unconditional strengthened original native no-long-bad-family comparison by genuine natural finrank induction; exceptional-proportion rough-step conclusion, GTZ correlation inverse and final target remain open')
Path(PREFIX+'-audit.py').write_text(source,encoding='utf-8')
Path(PREFIX+'-mathematical-review.txt').write_text('''JSP-000168 mathematical/application review, 2026-10-13

Classification: PROGRESS. Unconditional strengthened original native no-long-
bad-family statement proved. Original proportion comparison and StrongConjecture
remain UNPROVED. Author application/kernel build review, not independent replay.

1. Literal parameter source. roughParameterAffineSource is exactly the vector
affine substitution none->a+b*none, some j->0+1*some j. Its actual degree is
not increased. Scalar eval2 RingHom extensionality proves parameter specialization
at z is original specialization at a+b*z. Original vector projection/eval give
ALL raw spatial coefficient identities. This is not an inference from sampled
quotient equality, an assumed source model or a source chosen by its character.

2. Actual common original character. The already unconditional original
asymptotic character-production theorem supplies fixed finite S and A before
raw sources. Finite van der Waerden label thinning on subtype {chi // chi in S}
selects ONE chi on a+b*z with every index genuinely in the original range.
Empty S needs no special fake character: an actual bad input would produce an
impossible label. Raw pNew is the literal parameter-affine source and QNew is
the actual parameter-affine original map. Degree and all-real log identities,
actual original bad samples, ALL positive affine row bounds, size and rough
primorial coprimality survive. Requiring w>=the fixed input length makes b*diff
genuinely w-smooth. The same character controls ALL rows; no finite row truncation.

3. Original bad-family interface. NativeOriginalCommonBadFamily converts the
paper real-power ratios to genuine PowerDominates/eventual positivity using the
registered growth proof. Original family log equality in (z,y) becomes literal
all-real Option equality, so actual raw source/map enters common production.
Output is a true jointly polynomial reparametrized bad family with one common
original character and COMPLETE affine rows. No coefficient/test/box is fixed
prematurely or assumed independent of the original parameter index.

4. True top Lie geometry. Actual original rational stretched layer0=top proves
the top Lie-subalgebra rationality. Original horizontal annihilation of actual
commutator model, and actual adjoint generator lowering layer0 to layer1, prove
the required bracket annihilation. Nonzero original chi has a true vector
witness. Registered lattice-pivot normalization supplies rational V with chi(V)=1
and a POSITIVE integer K satisfying Exp(K*V) in ORIGINAL Gamma. Only this positive
power is asserted, not Exp(V) in Gamma. Every canonical residue kernel native
datum is actually constructed and has STRICT lower original finrank.

5. Actual horizontal kernel descent. The original character alone discharges
top rationality/bracket/integrality/nonzero-pivot fields of registered normalized
descent. Geometry/period/finite canonical child family/Part/Lip are chosen BEFORE
H, raw sources, scale indices, boxes or observables. The actual real bad-index
definition gives original lo,hi,residue,F. Exact real-to-complex embedding gives
same eta discrepancy and same norm/Lipschitz/geometry. Genuine finite choices
select actual samples and all affine row packets at each index; outside range,
defaults are guarded by the impossible range predicate. The old scalar model/
observable/pair-discrepancy inputs are thereby PRODUCED, not oracle premises.
Original full top group membership is proved through the true global-log iff.

6. Finite budgeting and genuine induction step. For EVERY chi in fixed S,
canonical normalization/descent is chosen before raw inputs. ALL its Fin K
children have strict original finrank drop, using actual normalized chi(V)=1.
Universal lower-native IH covers changed ordinary degree, geometry constants,
child Lipschitz bounds and scale Z/K; real-power growth is actually preserved.
For every child obtain positive no-bad length H_child. H=1+sum of ALL H_child
is positive even when S is empty. Child bad-family length restriction turns
eventual no-bad at H_child into no-bad at H. Finite dependent conjunction of
eventual thresholds is genuine, not an assumed uniform bound.

Every chi's actual descent then fixes N_chi for child target H. M=1+sum N_chi
is chosen BEFORE all raw sources, and common original character production
fixes the original length N_parent for target M. An actual original bad input
would produce ONE chi, actual reparametrized source/full affine rows at M, then
restrict to its N_chi and invoke actual kernel descent. Its actual child bad
family at H contradicts that SAME canonical child's genuine lower-IH threshold.
Different candidates' period/Part/Lip/scales need not be falsely identified.

7. Unconditional strong natural finrank induction. NativeNoLongBadFamily
strong-induces over r=actual Module.finrank R D.E, for ALL actual native data
at the original step bound. Dimension zero has registered genuine point-quotient
no-bad proof. Canonical children retain this step bound and strictly decrease r;
their ordinary degree and metric/data may change and are allowed by universal
IH. The final theorem NativeNoLongBadFamilyStatement D has NO IH/inverse/kernel/
character/model premise. It states: for every fixed data/dimension/ordinary
degree/bounded geometry and actual original real-power growth sequence, there
is one positive H and eventually NO original actual bad family of that length.
Source polynomials, coefficients, boxes, residues and tests are arbitrary after
the length and threshold. This is the strengthened bad-progression comparison.

8. Exact remaining gap. This is not yet the original bad-PROPORTION tends-to-zero
Proposition. Section 6 explicitly uses finite Szemeredi to extract arbitrary
prescribed bad progressions from a positive density in fixed index blocks.
Original residue-coordinate interval, partial block/tail, original smooth
step and literal jointly polynomial source must then match this theorem.
This dense extraction differs from finite COLOR van der Waerden already used.
Separate GTZ arbitrary-input interval Gowers linear-nilsequence correlation,
cube/Alignment and final FS/FP remain open. Fixed-data constants are not explicit
delta-power laws. The repaired source slab estimate is not unavoidable
obstruction. Old proof hashes/axioms, actual pins/six OpenAI source sections and
exact slab certificate are rechecked; standard axioms only. Author checks are
not independent replay/external peer review. Public repo/PR/prize not reached.
''',encoding='utf-8')
print(PREFIX)
