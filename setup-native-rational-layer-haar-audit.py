from pathlib import Path

prefix = 'round-native-rational-layer-haar'
modules = ['Hindman168/' + n + '.lean' for n in [
    'NativeRationalLayerOrbit', 'NativeRationalLayerHaarImage', 'NativeSubgroupMaximalCharacter']]
components = [
    'For EVERY layer of the ACTUAL final rational subgroup filtration and EVERY original rational residue representative, nativeRationalLayerOrbitData constructs the genuine ORIGINAL subgroup with the intersection of the ORIGINAL conjugated lattice. Actual compactness, native geometry, source metric and original step s come from proved constructors.',
    'The ACTUAL adapted polynomial is bundled into the ORIGINAL initial subgroup, with exact original exponential and logarithmic identities. No new polynomial source or source-membership oracle is introduced.',
    'nativeRationalLayerHaarImage is the image of the constructed normalized invariant probability under the ACTUAL original map x -> h*x*rho*Gamma. Exact evaluation, continuity, injectivity, compact orbit range, probability normalization, concentration on that orbit and invariance under h -> h*y for y in the SAME actual subgroup are proved. Empirical convergence, full support and face invariance are not inferred from these constructors.',
    'An actual nonzero rational functional on the initial subgroup, annihilating its internal brackets, has a TRUE greatest nonzero filtration level. Its restriction satisfies the EXACT NativeSubgroupRationalLevelCharacter predicate and vanishes on EVERY higher layer. Actual original conjugated-lattice intersection integrality implies rationality on the ORIGINAL lattice rational form by the proved positive-root intersection identity.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
    'Actual sequential smooth/irrational/periodic factorization is proved on ONE subsequence at the ORIGINAL step s. '
    'Actual layer subgroup/conjugated-lattice compact native data, original polynomial orbit inclusion, canonical '
    'Haar images and greatest-level rational character implications are now proved. Remaining: transport actual '
    'subgroup/cube horizontal inverse obstructions into these exact level characters and isolate the actual '
    'Taylor coefficients; actual simultaneous local point/cube-Haar laws through ORIGINAL s+1, sequence limit '
    'BEFORE locality alpha->0, projected Haar face invariance/full-support coset symmetry and actual joint face '
    'lifts/full Alignment; separate arbitrary-input GTZ interval Gowers LINEAR nilsequence inverse at sufficient '
    'native step; final positive distinct rapidly separated SAME-color ALL nonempty FS AND FP. '
    'No Haar law, source geometry, character, period, inverse or bound oracle is introduced. '
    'Author build/hash/axiom/source checks are not independent kernel replay or external peer review. '
    'No explicit delta-power law or other-marginal invariance is claimed. Public repository/PR/prize milestone not reached.')

assert Path(prefix + '-baseline.json').read_bytes() == Path('verification-manifest.json').read_bytes()
source = Path('round-native-periodic-factorization-audit.py').read_text(encoding='utf-8')
replacements = {
    'PREFIX=': repr(prefix),
    'OLD=': repr('round-native-periodic-factorization'),
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
source = source.replace('round-native-periodic-factorization-lakefile-before.toml', prefix + '-lakefile-before.toml')
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print(prefix)
