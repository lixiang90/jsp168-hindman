from pathlib import Path
import json

v = json.loads(Path('round-canonical-face-counting-checks.json').read_text())
assert not v['full_target_proved']
p = Path('CONTINUATION.txt')
s = p.read_text(encoding='utf-8').replace('Current batch: round-box-translation',
    'Earlier batch: round-box-translation')
start = s.index('Immediate next analytic work:')
end = s.index('Next algebra work:', start)
s = s[:start] + f'''Current batch: round-canonical-face-counting, verified 2026-10-11. Four modules, {v['new_theorems']} theorems, {v['new_definitions']} definitions; full build ({v['build_jobs']} jobs), {v['selected_axiom_reports']} selected transitive axiom reports, {v['project_modules']} project modules. Retained proof sources and axiom sets are unchanged, standard axioms only, all six pinned paper sections match their Git objects. This is author-side verification, not independent kernel replay.
- AlignmentCanonicalShiftScale proves fixed d eventually divides the literal alignmentPairProgression and abs(Delta)<=epsilon*alignmentCubeScale, uniformly over all rough tuples in earlier cutoffs and all adding pairs. It uses actual alignmentPairResidue_master_data, which already identifies the canonical representative, and alignmentPairProgression_exact. There is no need to reprove uniqueness or use an existentially chosen rho. The scale proof uses abs(M*Delta)<=2*aux^3, master growth, positive M, and dyadic lower product>=1.
- AlignmentSingleCoordinateTranslation reduces the coordinate-sum estimate to 4*K*abs(Delta)/(c*Z) with arbitrary signed residues and endpoints.
- AlignmentCanonicalFaceCounting combines divisibility and smallness with d<=c*Z/2 (retained-step growth at q=1) to prove error<=epsilon. One threshold precedes all tuples, adding pairs, shifted coordinates, side-bounded integer boxes, residues and bounded complex tests. It uses K+1 so K=0 is included.
- AlignmentRawFaceCounting discharges roughness and cutoffs using actual globalRawMass support and existing support geometry. It proves the same uniform counting error for every raw-supported sample. The theorem is a residue-box coordinate translation statement, not conditional face invariance or rough-step removal. Its c*Z lower side is supplied by the earlier permitted-real-box geometry after replacing c by c/2.

Review: actual Delta divisibility and growth are now connected, completing the counting part of pinned 08_alignment lines 550-567. Full face invariance still needs the native face identity, smooth test bounds, rough-step comparison and posterior transfer. Native translations and readings already exist: AlignmentNativeJointTranslations.alignmentNativeJointModelCosetOrbit_translation shifts k_i by sum_j v_ij*Delta_ij; AlignmentNativeJointReadings has modelOrbit, bound and translation theorems. Combine these with cube vertices and own-target filtering rather than postulating a generic transformation law.

Immediate next substantial work: prioritize the uniform-degree native logarithm polynomiality required by rough-step removal. Existing NativeLieRationalProductCurve.nativeLieRationalProductPolynomial is literally nativeLieRationalPicardPolynomial w u (nilpotencyClass+1), and evaluates to the genuine global logarithm of Exp(u)*Exp(t*w). The Picard list starts [(0,u)] and recurses by appending the primitive of nativeLieRationalFieldPolynomial applied to the preceding list and [(0,w)]. No finite vector polynomial degree API was found yet in FiniteVectorPolynomial*.lean. Add explicit exponent support bounds for list append, primitive and bilinear composition, then bound the finite adjoint/defect/field recursion and Picard recursion by a function of nilpotency class. Coefficients need no bound. This addresses the actual joint-log-polynomial obligation rather than more geometric wrappers. Preserve the exact native group interpretation and eventual composition/recovery obligations described below.

''' + s[end:]
p.write_text(s, encoding='utf-8')
print('Updated continuation checkpoint from verified counts.')
