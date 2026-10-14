from pathlib import Path
import json

prefix = 'round-native-periodic-factorization'
modules = ['Hindman168/' + n + '.lean' for n in [
    'NilpotentUniformPowerCore', 'SignedFallingPeriod', 'NativeSignedRightGenerators',
    'NativeRightFiniteWords', 'FiniteSequenceFreeze', 'NativeRightCosetPeriod',
    'NativeSequentialPeriodicFactorization']]
components = [
    'A genuine finite normal-core quotient is proved from the actual rational hull and finite generator list. The ORIGINAL lattice is not assumed normal, and no discreteness, finite-index or period oracle is supplied.',
    'The literal original right factors at EVERY signed integer input are exactly integer powers of fixed rational generators with factorial absorbed in their fixed vectors. ALL unbounded signed integer correction coefficients and the actual reverse product order are retained.',
    'ONE positive period covers EVERY original sequence index and EVERY signed integer input in the ORIGINAL lattice coset space. A finite-pattern subsequence selects actual rational representatives from its genuine first sample.',
    'The SAME final subsequence preserves the original filtration, ALL rational-character limits, compact constants, scaled coefficient limits, exact ALL-real group identities, original group compact-open smooth limits, log-coordinate C1 limits and actual native body-velocity limits/bounds. Original step-s left-linear orbit application is proved without stretching.',
    'NativeSequentialPeriodicFactorization is unconditionally proved for the original adapted input. Its exact original quotient bridge removes only the final right lattice factor and transfers the frozen right coset using actual cancellation, without any global normality assumption. This closes the smooth/irrational/periodic sequential factorization obligations of pinned section 7; local cube-Haar laws and StrongConjecture remain unproved.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
    'The actual original sequential smooth/irrational/periodic factorization is now proved on ONE subsequence, '
    'with the same final rational filtration and exact original step. Remaining: actual simultaneous local '
    'point/cube-Haar laws through ORIGINAL s+1, sequence limit BEFORE locality alpha->0, projected Haar face '
    'invariance/full-support coset symmetry and actual joint face lifts/full Alignment; separate arbitrary-input '
    'GTZ interval Gowers LINEAR nilsequence inverse at sufficient native step; final positive distinct rapidly '
    'separated SAME-color ALL nonempty FS AND FP. No source geometry, period, Haar, inverse or bound oracle '
    'has been introduced. Author build/hash/axiom/source checks are not independent kernel replay or external '
    'peer review. No explicit delta-power law or other-marginal invariance is claimed. '
    'Public repository/PR/prize milestone not reached.')

baseline = Path('verification-manifest.json').read_bytes()
Path(prefix + '-baseline.json').write_bytes(baseline)
Path(prefix + '-lakefile-before.toml').write_bytes(Path('lakefile.toml').read_bytes())
source = Path('round-native-smooth-factor-limits-audit.py').read_text(encoding='utf-8')
replacements = {
    'PREFIX=': repr(prefix),
    'OLD=': repr('round-native-smooth-factor-limits'),
    'BASELINE=': repr(prefix + '-baseline.json'),
    'MODULES=': repr(modules),
    'COMPONENTS=': repr(components),
    'REMAINING=': repr(remaining),
}
lines = []
for line in source.splitlines():
    key = next((key for key in replacements if line.startswith(key)), None)
    lines.append(key + replacements[key] if key else line)
source = '\n'.join(lines) + '\n'
source = source.replace('round-native-smooth-factor-limits-lakefile-before.toml', prefix + '-lakefile-before.toml')
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'prefix': prefix, 'modules': modules}))
