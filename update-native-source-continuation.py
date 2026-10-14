from pathlib import Path
import json

prefix='round-alignment-native-source'
manifest=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert manifest['build_log']==prefix+'-build.txt'
checks=json.loads(Path(prefix+'-checks.json').read_text(encoding='utf-8'))
assert not checks['full_target_proved'] and checks['standard_axioms_only']
path=Path('NATIVE-ORIGINAL-ROUGH-PROPORTION-CONTINUATION.txt')
note=path.read_text(encoding='utf-8')
note=note.replace('Continuation after round-alignment-native-window.', 'Continuation after round-alignment-native-source, 2026-10-14.')
new='''ACTUAL NATIVE SOURCE CONNECTION, NOW PROVED:
SingletonChartNativeExponential identifies a genuine exponential coordinate
homeomorphism with the native Lie exponential using its actual singleton-chart
differential, original ray subgroup law and ODE uniqueness. Native log is its
genuine inverse, not a renamed coefficient function.
AlignmentArrayNativeCoordinates packages the same genuine array group/lattice/
step/compatible metric for actual small finite indices and ANY original native
model universe. The typed coefficient equivalence proves native global log
equals the original coefficient log after applying that equivalence. Only
previously proved canonical structures are bound locally, with no new instance
declaration, source edits to old proofs or compiler limit changes.
NativeVectorPolynomialSource constructs the native exponential source of the
actual finite vector polynomial, proves the ALL-REAL log identity and proves
sample equality from genuine scalar/basis coordinate identities.
AlignmentExposedNativeVectorPolynomial assembles the EXISTING exposed scalar
joint-log polynomials in a FIXED basis of the actual native array model.
Its degree is ((s*s+1)^(s+1))*max(1,T.card), independent of coefficients/w;
exposure-key freezing and exact native log evaluation on original cube arrays
are proved. AlignmentExposedNativeSource proves that the exponential extension
equals the ORIGINAL actual cube array at every permitted sample.
RoughVectorMvSubstitution proves genuine linear variable changes preserve
degree and exact vector evaluation. RoughRemovedFactorPolynomial makes ONLY
the removed j free, freezes ALL other factors and keeps all spatial variables.
It ignores the dummy frozen value at j, by a proved update invariance theorem.
AlignmentRemovedFactorNativeSource builds this actual single-factor source,
proves the original actual-cube sample identity, and constructs the spatial
x=residue+q*y residual degree/log packet outright. No polynomial/log packet
or analytic comparison is assumed. q and residue are fixed while j varies.
Explicit DecidableEq binders reconcile actual Fin updates with generic updates;
they add no arithmetic constraint or custom instance.
These are genuine SINGLE-MODEL source results; finite JOINT source and test
synthesis and the full conditional bad-event application still need proofs.

NEXT MAIN ROUTE:
1. Finish actual JOINT native source/fiber and observable synthesis.
   Use the new exact single-model sources, not assumed scalar/global-log
   compatibility. NativeVectorPolynomialSource and the new residual packet
   discharge all-real polynomial/log premises. Fixed bases exist from the
   genuine finite-dimensional model, before w/source coefficients.
   Build the heterogeneous finite joint native source with its true group,
   model and lattice. Existing useful components: AlignmentNativeJointLieGroup,
   AlignmentNativeJointNilmanifold, AlignmentNativeJointModelOrbit and
   AlignmentNativeJointReadings. Watch their universe signatures: do not
   silently force arbitrary original models to universe zero. A genuine
   product of native data is also available: nativeNilmanifoldProduct,
   RoughVectorMvPairPolynomial and NativeProductExponential.
   Reindex the actual spatial Option(cube coordinates) to Fin(m) using a
   genuine finite equivalence, preserving residue classes, means and boxes.
   Assemble the fixed joint quotient tests (including fixed face transforms)
   and justified Lipschitz/sup bounds before sampling data.
   AlignmentMasterRetainedCRT already proves genuine retained representatives
   and update invariance when removed j is not in retained U; USE these.
   AlignmentPermittedRetainedGeometry supplies actual transformed endpoints.
   Derive bounded normalized-scale ranges on ALL actual posterior dyadic
   supports, apply the proved ALL-ANCHOR native window cap, and prove actual
   bad-event inclusion/union under the genuine posterior law. No gcd(q,t)
   restriction is allowed; retained q/residue must stay independent of t.
   Full cube/face/Alignment synthesis remains required.

'''
start=note.index('NEXT MAIN ROUTE:')
end=note.index('2. Separate GTZ interval Gowers correlation inverse remains unproved.')
note=note[:start]+new+note[end:]
marker='LATEST TERMINAL AUDIT,'
note=note[:note.index(marker)]
note+='LATEST TERMINAL AUDIT, 2026-10-14: '+prefix+'.\n'+json.dumps(checks,indent=2)+'\n'
note+='This goal turn added 8 modules, 29 theorems and 11 definitions in one\nterminal author audit round. Every prior registered proof and axiom set is\nunchanged. No audit/compiler process remains active after terminal completion.\n'
note+=manifest['last_round']['remaining']+'\n'
path.write_text(note,encoding='utf-8')
print('Updated actual native-source continuation after recorded terminal audit.')
