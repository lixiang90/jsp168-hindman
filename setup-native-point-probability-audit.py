from pathlib import Path
prefix = 'round-native-point-probability'
old = 'round-native-point-mixture'
modules = ['Hindman168/'+name+'.lean' for name in [
'UnitIntervalProbability','FiniteProbabilityMixture','NativeRationalCurveHaarImage',
'NativePointMixtureMeasure','UnitLipschitzProbabilityConvergence','FiniteEmpiricalProbability',
'NativeOriginalPointWeakLimit','NativeSequentialPointWeakLimit','NativeOriginalContinuousPointMixture']]
components = [
'Constructed the ACTUAL curve-averaged subgroup Haar image as pushforward of unit-interval length probability times actual subgroup Haar probability; proved probability mass and complex continuous integral formula via measurable maps and Fubini.',
'Constructed the uniform finite residue mixture as an actual measure; proved mass one for positive period and the exact 1/M integral formula. No measure-valued integration oracle or assumed mixture exists.',
'Proved complex unit Lipschitz testing implies weak convergence of probabilities on compact metric spaces by fixed test-dependent normalization and the mathlib Portmanteau theorem. The normalizing constant is strictly positive; rescaling and real projection are exact.',
'Constructed actual empirical probabilities, with explicit fixed-point fallback for empty windows. Cofinality makes the ORIGINAL floor-window eventually nonempty; its integral is the true finite sum divided by its true cardinality.',
'Proved weak probability convergence of the ORIGINAL source on the SAME factorization subsequence, retaining both local laws, final filtration, positive period, rational residues and smooth curve. Also proved the original scalar point-mixture formula for EVERY continuous complex test without new extraction.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
'Original q=0 local laws, actual global floor-window point-mixture probability weak convergence and '
'all-continuous complex testing are proved on one original subsequence with SAME final filtration/period/sigma/h. '
'Remaining: actual SAME-filtration cube subgroup geometry and face-character coefficient isolation, '
'simultaneous local cube laws through ORIGINAL s+1 with length before locality, projected face '
'invariance/full support, joint lifts/full Alignment; separate arbitrary-input GTZ interval Gowers '
'LINEAR nilsequence inverse; final positive distinct rapidly separated SAME-color ALL nonempty FS AND FP. '
'No Haar/source/cardinality/partition/inverse oracle or new axiom introduced. Author checks are not '
'independent kernel replay or external peer review. No global metric Lipschitz or quantitative locality '
'rate claimed. Public repository/PR/prize milestone not reached.')
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
Path(prefix+'-mathematical-review.txt').write_text('Author mathematical review, 2026-10-14.\nPinned OpenAI 07_cube_limits.tex: the q=0 joint-point-law limit.\nThis round packages that established scalar limit as actual probability\nweak convergence, without altering the source or choosing another subsequence.\n\nThe base measure is Lebesgue measure restricted to Ioc 0 1, mass exactly one.\nIts product with the ACTUAL rational-layer orbit subgroup Haar probability\nis pushed to the original quotient by (beta,x) -> h(beta)*x*rho*Gamma.\nJoint continuity in the compatible quotient metrics implies measurability.\nAll continuous observables on the compact original quotient are bounded,\nso the integrability premise of Fubini is proved, not assumed. The resulting\nintegral is exactly the interval integral of the original Haar-image test.\n\nResidues are averaged by inverse cardinality times the finite measure sum.\nPositive M supplies a nonempty index type and legitimizes reciprocal mass\ncancellation. The integral formula also holds for the empty finite index\ncase, but the probability claim explicitly REQUIRES nonemptiness. The actual\nnormalizer is 1/M, not a symbolic average axiom.\n\nUnit complex Lipschitz convergence is upgraded via the existing proved\nPortmanteau theorem. A real Lipschitz test is embedded into complex numbers;\nits compact-space sup norm and Lipschitz constant give the strictly positive\nscale R = norm(F)+K+1. Scaling precedes all sequence limits and is reversed\nalgebraically, before taking the real part. No density, uniform radius or\nrate is assumed; no new subsequence depends on the test.\n\nEmpirical probability uses the ACTUAL sample finite set subtype and its\ncardinality, with Dirac masses at the original orbit points. For empty\nwindows it is a specified fixed Dirac probability; no division-by-zero\nmeasure is claimed to be a probability. Cofinality L -> infinity proves\n1 <= floor(L) eventually, so this fallback does not affect the limit.\n\nThe sequential theorem takes original D,F,L,p and adaptation, reuses the\nSAME witnesses of the original local theorem, and retains both residue and\nreal-window local laws. The limiting measure really is the curve/residue\nHaar mixture defined above. Every continuous complex test follows from\nweak convergence using compactness and bounded continuous test topology.\n\nThis settles the probability/all-continuous API for q=0 only. Positive\ncube dimensions, simultaneous laws through original s+1, projected face\ninvariance/full support, joint lifts/full Alignment, separate GTZ inverse,\nand final SAME-color positive distinct rapidly separated ALL nonempty FS\nand FP remain unproved. No unavoidable obstruction or full theorem claim.\nAuthor checks are not independent kernel replay or external peer review.\n', encoding='utf-8')
print(prefix)
