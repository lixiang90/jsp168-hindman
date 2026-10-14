from pathlib import Path
import json
prefix='round-alignment-native-cube-removal'
manifest=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert manifest['last_round']['review_file']==prefix+'-review.json'
summary=json.loads(Path(prefix+'-checks.json').read_text(encoding='utf-8'))
p=Path('NATIVE-ORIGINAL-ROUGH-PROPORTION-CONTINUATION.txt')
s=p.read_text(encoding='utf-8')
s=s.replace('Continuation after round-alignment-native-posterior','Continuation after '+prefix,1)
completed="""COMPLETE PERMITTED-BOX REMOVAL COMPARISON, NOW PROVED:
AlignmentJointSourceRestriction proves the ALL-REAL actual one-factor source
at its actual factor equals the SAME full joint spatial source. Actual integer
sample equality remains distinct from off-sample original orbit assertions.
OriginalIntegerResidualBoxGeometry obtains exact native real residual geometry
from the ORIGINAL integer cube endpoints, positive q, q<=CubeScale and CRT
representative bounds. Endpoints/sample sets are unchanged. No sign assumption
on the generic endpoint bound constant is required.
AlignmentActualOriginalResidualGeometry derives every retained-subset box
condition from actual rounded cube bounds, actual raw supports and master
scale growth. AlignmentTailTupleOriginalData preserves original retained
products and CubeScale when filling anchor values outside tail T.
NativeRealResidualGoodMean turns the original non-strict bad-event complement
into a strict bound on the SAME normalized fine/coarse complex means.
AlignmentJointTailResidueMean defines literal same-source/same-endpoint means
on retained CRT grids and proves each exact one-factor good-event discrepancy.
AlignmentJointActualRemovalStep discharges its geometry and all fine/coarse
CRT arithmetic under original raw supports and original exposure keys. No
analytic cap, degree/log packet or gcd(retained,removed) is assumed.
OrderedRemovalTelescope uses U(j)={k in T | j<k} with genuine subset/exclusion
and Finset induction on the minimum. All adjacent differences use one set
function. Empty chains have zero cost and no removal direction is invented.
AlignmentJointActualRemovalChain telescopes the COMPLETE original permitted
cube-box means from full tail T to denominator-only step d, with exact
T.card*eta cost. A shared explicit mean function resolves Lean reduction;
compiler options/heartbeats/native structures remain unchanged.
AlignmentJointOriginalBoxRemovalFailure quantifies over ALL original permitted
boxes and all tests in the ACTUAL original joint observation-family image.
AlignmentJointOriginalBoxRemovalPosterior uses the actual posterior support
and key to prove inclusion in the earlier genuine direction failure union.
With eta=epsilon/(T.card+1), COMPLETE box/mean removal failure vanishes
uniformly under the original short-exposure posterior. No event narrowing,
endpoint change, fabricated nonempty probability or assumed analytic estimate.
AlignmentJointOriginalBoxRemovalFiniteChoices allows every fixed finite
original residue-choice list selected after exposure, with cardinality cost
before the cutoff. Empty lists remain empty.
AlignmentOriginalCubeCRTMean proves congruent residue vectors give equal WHOLE
box sets, and the FULL original affine cube sample mean equals the full-tail
CRT-grid mean for arbitrary sample readings. This includes algebraic empty
means, with no changed endpoint, dense subsample or gcd between factors.
The final specialization of that scalar identity to actual original product
observations and exposed origin/denominator labels still needs assembly.

"""
s=s.replace('NEXT MAIN ROUTE:\n',completed+'NEXT MAIN ROUTE:\n',1)
a=s.index('1. Match actual permitted cube means and telescope the full removal chain.')
z=s.index('2. Separate GTZ interval Gowers correlation inverse',a)
s=s[:a]+"""1. Close the ORIGINAL product-observation cube-law interface and face invariance.
   Full same-source/same-endpoint factor-removal telescope and actual posterior
   uniform permitted-box failure vanishing are now PROVED. Do not redo these.
   Use AlignmentJointOriginalBoxRemovalPosterior/FiniteChoices directly.
   AlignmentOriginalCubeCRTMean is the exact whole-grid scalar mean identity.
   Specialize its f to the actual full joint spatial-source reading and the
   registered original joint integer sample/complex reading equalities.
   Original origin rho must stay exposed/fixed before removed t varies:
   alignmentShortExposureKey_arrayResidue_eq identifies actual tau*p % M
   with the exposed anchor residue when p has the original pivot M residue.
   alignmentMicrocellFirst_modEq supplies actual microcell-first residue.
   Denominator choices may be selected after sampling, so use the FULL fixed
   finite list, e.g. Option(cube direction)->Fin d, with d>0 and integer mod
   representatives. Do not assume an unbounded data-dependent origin can be
   unioned into the fixed finite list. The origin is genuinely frozen by key.
   Terminal step-d mean retains only the original d residues; at retained=1
   the CRT residue is congruent to the original choice mod d.
   Next prove actual integer spatial array/read correspondence on coarse grids,
   and original upper-face array-slot shift equals the spatial Delta_e translate.
   Original array exponents have integral correction terms from the exposed
   residue and actual raw factors. Do not infer integer orbit equality solely
   from all-real log-polynomiality. Original declared native model/array log
   evaluation theorems should discharge these genuine integrality identities.
   Terminal d-grid translation changes means by original boundary count error;
   derive d|Delta_e and uniform |Delta_e|/CubeScale ->0 from actual master data.
   Comparing on both sides, and fixed continuous face-composed test families,
   gives original marginal face invariance; do not assert other-component
   invariance. Then full cube limits, Alignment, countable diagonal and final
   strongly separated common-color FS/FP remain work.

"""+s[z:]
s=s[:s.index('LATEST TERMINAL AUDIT,')]+ 'LATEST TERMINAL AUDIT, 2026-10-14: '+prefix+'.\n'+json.dumps(summary,indent=2)+'\n'
s+='This goal turn added '+str(manifest['last_round']['new_module_count'])+' modules, '+str(summary['new_theorems'])+' theorems and '+str(summary['new_definitions'])+' definitions in one terminal author audit round.\n'
s+='Every prior registered proof and axiom set is unchanged. No audit/compiler process remains active after terminal completion.\n'
s+=manifest['last_round']['remaining']+'\n'
p.write_text(s,encoding='utf-8')
print(prefix)
