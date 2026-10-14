from pathlib import Path
import json
prefix='round-alignment-original-product-law'
manifest=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert manifest['last_round']['review_file']==prefix+'-review.json'
summary=json.loads(Path(prefix+'-checks.json').read_text(encoding='utf-8'))
p=Path('NATIVE-ORIGINAL-ROUGH-PROPORTION-CONTINUATION.txt')
s=p.read_text(encoding='utf-8')
s=s.replace('Continuation after round-alignment-native-cube-removal','Continuation after '+prefix,1)
completed="""LITERAL ORIGINAL PRODUCT CUBE LAW CONNECTION, NOW PROVED:
AlignmentJointFullSpatialReadings proves all-real full-source tail congruence
and exact ORIGINAL simultaneous nilsequence product reading at every valid
integer cube sample, including empty tails. No removed tail direction is
chosen to handle an empty tail, and no off-sample integer orbit is asserted.
AlignmentJointOriginalProductCubeMean defines the LITERAL original nilsequence
product cube average and proves it equals the COMPLETE full-tail CRT joint
mean. Actual raw supports derive tail positivity and coprimality with M/d.
The original key/pivot residue identifies tau*p mod M with the EXPOSED anchor
origin. Every original sample, endpoint, slot and observation is preserved.
AlignmentOriginalDenominatorChoices constructs the FULL fixed finite list
Option(kappa)->Fin d, d>0. Actual sample-selected denominator choice is EXACTLY
its integer remainder and has its original congruence, selected AFTER sampling.
Terminal retained=1 is the genuine step-d box with only original d residues;
there is no origin restriction or fake positive mass on an empty box.
AlignmentJointMetricProductBounds proves original product reading sup bound
is the product of original component bounds on EVERY joint quotient point.
No numerical Lipschitz bound on source/projection/composed reading is assumed.
AlignmentJointTerminalGridMeans defines literal terminal d and spatially
translated d means, proves exact retained-empty identity and the original
normalized boundary-count translation bound on whole grids.
AlignmentJointActualTerminalTranslation derives actual d|Delta, uniform
|Delta|/CubeScale smallness, positive/large side geometry and the product
reading bound from original master/raw data. ONE uniform cutoff before source
data, endpoints/residues, every own pair/coordinate and original observers
makes the actual terminal-grid translation error < epsilon. No desired
analytic cap or source coefficient bound is provided as hypothesis.
AlignmentOriginalProductRemovalFailure now records the LITERAL original
nilsequence product cube law versus its genuine terminal d law. It quantifies
ALL original permitted boxes, original residue samples and original numerical
bounded/Lipschitz observer classes. The denominator label may depend on sampled
factor, pivot or microcell, and lies in the FULL fixed finite list.
AlignmentOriginalProductRemovalPosterior identifies exact original/full-CRT
and terminal-grid means on the actual posterior support and includes this
failure in the PROVED finite-choice original joint failure union. Uniform
posterior removal vanishing is now an actual original product cube-law result.
The origin stays exposed/fixed; do not union an unbounded data-dependent origin.
This still does NOT prove original upper-face array-slot automorphism equals
the spatial Delta translate, or full original marginal face invariance.

"""
s=s.replace('NEXT MAIN ROUTE:\n',completed+'NEXT MAIN ROUTE:\n',1)
a=s.index('1. Close the ORIGINAL product-observation cube-law interface and face invariance.')
z=s.index('2. Separate GTZ interval Gowers correlation inverse',a)
s=s[:a]+"""1. Prove actual coarse integer state / upper-face slot correspondence.
   Literal original product cube mean and complete d-grid removal agreement
   under actual posterior, including sampled denominator choices, are now
   PROVED. Actual terminal d-grid Delta translation error is also PROVED.
   Use AlignmentOriginalProductRemovalPosterior and
   AlignmentJointActualTerminalTranslation; do not redo those comparisons.
   The remaining structural step is ACTUAL spatial integer array/model identity
   on coarse grids and its original upper-face array-slot automorphism.
   Use alignmentNativeModelLogPolynomial_eval with genuine integral base and
   increment exponents. Original exposed base formula reads integer
   X=z_none+sum weight*z_some, plus Y and (rho+tau*s-rho_s)/M.
   Prove that correction integral from original residue correction and key;
   use actual alignmentPairProgression for own pairs, zero for non-own pairs.
   All-real log-polynomiality alone is NOT an integer nilsequence identity.
   Then source at every integer spatial point equals the literal original
   native ModelArray(k,Delta) in every component, through the actual bases,
   coefficient-log/native-log identity and product/source sample interface.
   Original alignmentNativeModelArray_input_translation and native array
   slot translations are already proved. For spatial coordinate j shifted by
   Delta_e, each vertex/component gets weight(j)*Delta_e; slot translation
   weight(j)*unit_e gives that SAME change when e is an OWN pair of T.
   Original 0/1 vertex weights specialize it to the desired upper face.
   Construct/transport genuine typed product-native quotient slot maps and
   their actual metric continuity; preserve the original product/pointwise
   lattices, with no normality or numerical projection Lipschitz assumption.
   Face-composed original test families need fixed compact/Lipschitz
   approximation BEFORE sources/endpoints. Existing general compact-family
   and original-test cap infrastructure should be reused.
   Comparing both sides yields original MARGINAL face invariance only;
   do not assert other-component invariance. Then full cube limits, Alignment,
   countable diagonal and final strongly separated common-color FS/FP remain.

"""+s[z:]
s=s[:s.index('LATEST TERMINAL AUDIT,')]+ 'LATEST TERMINAL AUDIT, 2026-10-14: '+prefix+'.\n'+json.dumps(summary,indent=2)+'\n'
s+='This goal turn added '+str(manifest['last_round']['new_module_count'])+' modules, '+str(summary['new_theorems'])+' theorems and '+str(summary['new_definitions'])+' definitions in one terminal author audit round.\n'
s+='Every prior registered proof and axiom set is unchanged. No audit/compiler process remains active after terminal completion.\n'
s+=manifest['last_round']['remaining']+'\n'
p.write_text(s,encoding='utf-8')
print(prefix)
