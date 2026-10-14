from pathlib import Path

prefix = 'round-native-window-haar'
old = 'round-native-point-haar'
modules = ['Hindman168/'+name+'.lean' for name in [
    'NativeSubgroupAffineTopCoefficient', 'NativeRationalLayerWindowHaar',
    'NativeSubgroupIrrationalScale', 'NativeRationalLayerRealWindowHaar']]
components = [
    'The actual scalar projection has totalDegree at most the highest surviving level, proved directly from ORIGINAL aggregate vector coefficients and the next-layer kernel. Arbitrary affine origins leave that top coefficient unchanged, and a fixed dilation d multiplies it by d^j. The exact value is d^j times the ORIGINAL Taylor character value divided by j factorial.',
    'Uniform q=0 subgroup Haar convergence now covers EVERY real origin and EVERY natural window length at least tau times the original cofinal natural scale, for ANY fixed nonzero rational step and fixed 0<tau<=1. The original character grid, bound and eventual threshold precede ALL origins, window lengths and unit Lipschitz tests. Fixed signed integer progressions are included.',
    'The rational multiplier d^j/j! is applied INSIDE the circle character using the proved all-rational-level irrationality. Window-length comparison occurs only OUTSIDE the norm via the genuine power comparison. No division of circle norm by d, bounded-origin assumption or additional source irrationality is used.',
    'Actual character escape is retained under any eventually positive fixed lower comparison of REAL scales. Natural floor of a cofinal real scale satisfies the required half-scale comparison. This proves the same uniform translated progression-window q=0 Haar law directly from the ORIGINAL REAL-scale sequential factorization irrationality.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
    'Actual smooth/irrational/periodic sequential factorization, original subgroup horizontal/level transport '
    'and exact original Taylor top coefficients are proved. Uniform q=0 Haar laws now cover ALL real origins, '
    'fixed nonzero rational steps (hence signed integer progression restrictions), and ALL windows whose '
    'length is at least a fixed positive fraction of the ORIGINAL cofinal REAL scale. Remaining: actual '
    'smooth-factor/Haar-image transport, continuous and compact observable families and point-law assembly; '
    'actual SAME-filtration cube subgroup geometry and face-character coefficient isolation, simultaneous '
    'local cube-Haar laws through ORIGINAL s+1, sequence limit BEFORE locality alpha->0, projected Haar '
    'face invariance/full-support coset symmetry, joint face lifts/full Alignment; separate arbitrary-input '
    'GTZ interval Gowers LINEAR nilsequence inverse at sufficient native step; final positive distinct '
    'rapidly separated SAME-color ALL nonempty FS AND FP. No Haar/source/character/period/inverse/bound '
    'oracle introduced. Author build/hash/axiom/source checks are not independent kernel replay or external '
    'peer review. No explicit delta-power law or other-marginal invariance is claimed. Public repository/PR/prize milestone not reached.')

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
Path(prefix+'-mathematical-review.txt').write_text('''Author review, 2026-10-14.
Pinned OpenAI 07_cube_limits.tex: q=0 part of local cube law, coefficient
isolation and fixed progression restrictions. This is still NOT the full
local cube proposition or the original Hindman theorem.

The scalar degree bound uses the actual aggregate weighted coefficients.
It is valid even when the raw vector-polynomial list has zero vector terms
of arbitrarily high scalar degree. Affine translation therefore cannot
change the surviving top coefficient, regardless of the size of its origin.

The progression step d is a FIXED nonzero rational; its power divided by
the factorial is a nonzero rational multiple of the same geometric level
character. The existing all-rational-level irrationality supplies its exact
escape. We never divide circle norms by step sizes. Negative steps are
allowed and do not enter the positive window-length comparison.

The actual inverse is applied to the genuinely affine-reparametrized original
source. Weight preservation and all-real source equality are proved, not
assumed. The original subgroup, conjugated lattice and filtration remain.
Finite grids and eventual intersections precede every origin b, length m
with tau*N<=m, and every unit Lipschitz test, even when all vary with n.

The inequality finite_coefficient_scale_transfer compares N^j and m^j
outside the norm with a fixed tau^-ell budget. Positivity of m follows
from eventual N>0, tau>0 and the stated length bound. No upper bound on m
or origin b is needed for the subgroup law proved here.

For cofinal real L, floor(L)>=L/2 eventually is derived from L>=2 and the
actual strict floor lower bound. All-character escape is preserved under
this positive scale comparison. floor(L) is cofinal and floor(L)<=L
eventually, so the real-scale result follows with the exact requested
window lower bound. No assumption that L is integral is introduced.

Still missing: smooth factors and original Haar-image comparison, compact
families of pullback tests, actual cube native geometry, face restrictions,
locality-limit order and all later alignment/Gowers/final FS-FP obligations.
This round establishes mathematical progress, not an unavoidable barrier.
No independent kernel replay or external peer review is claimed.
''', encoding='utf-8')
print(prefix)
