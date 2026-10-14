from pathlib import Path
import json
import re

prefix = 'round-rough-smooth-affine'
modules = [
    'Hindman168/DiscreteCosetProductSmooth.lean',
    'Hindman168/RoughNativeConjugateOrbitSmooth.lean',
    'Hindman168/RoughMvAffineSubstitution.lean',
    'Hindman168/RoughSpatialSubstitution.lean',
    'Hindman168/RoughNativeAffineKernelCoordinates.lean',
]
components = [
    'DiscreteCosetProductSmooth proves smooth descent with an arbitrary additional manifold parameter from the actual quotient projection. Both variables vary jointly and the discrete subgroup need not be normal.',
    'RoughNativeConjugateOrbitSmooth proves joint smoothness of the actual induced map (ell,h Delta) maps to ell*h*g Gamma, using the original native subgroup inclusion and actual discrete coset charts for the conjugate intersection.',
    'RoughMvAffineSubstitution proves total degree does not increase under arbitrary linear polynomial substitution over a commutative semiring, constructs coordinatewise affine substitution, and proves exact scalar and vector evaluation and degree transport.',
    'RoughSpatialSubstitution instantiates the joint substitution with an unchanged progression parameter z and spatial coordinates x=u+K*y. Evaluation and total degree transport are proved including zero K and empty spatial index types.',
    'RoughNativeAffineKernelCoordinates combines the original native kernel logarithm coordinate theorem with the actual spatial substitution. The resulting coordinate polynomial evaluates to the original log Q_z(u+K*y) for every real z,y, with the same coefficient-independent uniform degree bound.',
]
baseline = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
remaining = baseline['last_round']['remaining']
remaining = remaining.replace('Uniform quantitative Lipschitz induced-observable bounds, slow-factor freezing and sampling estimates remain open.', 'Joint smoothness of the actual induced orbit map and degree-preserving affine spatial substitution of the actual kernel logarithm are now proved. Uniform quantitative Lipschitz induced-observable bounds, slow-factor freezing and sampling estimates remain open.')
if 'Joint smoothness of the actual induced orbit map' not in remaining:
    remaining = 'Joint smoothness of the actual induced orbit map and degree-preserving affine spatial substitution of the actual kernel logarithm are now proved. ' + remaining
remaining = remaining.replace('affine spatial substitution, ', '')
remaining = remaining.replace('Smoothness and a uniform quantitative Lipschitz bound for induced tests are not proved by continuity or compactness and remain open, along with slow-factor freezing, sampling estimates, assembly of scalar models and affine spatial substitution.', 'The uniform quantitative Lipschitz bound for induced tests, slow-factor freezing, sampling estimates and assembly of scalar models remain open; smoothness alone does not close these quantitative obligations.')
source = Path('round-rough-conjugate-lattice-audit.py').read_text(encoding='utf-8')
replacements = {
    'PREFIX': repr(prefix), 'OLD': repr('round-rough-conjugate-lattice'),
    'MODULES': repr(modules), 'COMPONENTS': repr(components), 'REMAINING': repr(remaining),
}
for name, value in replacements.items():
    source, count = re.subn('^' + name + '=.*$', lambda _: name + '=' + value, source, flags=re.M)
    if count == 0:
        source, count = re.subn('^' + name + ' =.*$', lambda _: name + ' = ' + value, source, flags=re.M)
    assert count == 1, name
a = source.index('application_review=COMPONENTS+')
b = source.index('verified=summary', a)
review = [
    'Section 06 rough-kernel-test requires smoothness on the actual smaller quotient. The map uses the actual conjugate intersection and the original multiplication order. The additional left parameter is included in the smooth descent theorem; separate smoothness was not substituted for joint smoothness.',
    'The subgroup and quotient chart instances are explicit. Smoothness is derived from the original smooth subgroup inclusion, group multiplication and quotient projection; no new smooth structure on an unrelated space is used.',
    'Smoothness alone does not supply the numerical uniform Lipschitz estimate required for the full rough-step induction. Compatible metrics and derivative bounds remain a separate obligation, as do slow-factor freezing and sampling comparison.',
    'The affine substitution leaves z unchanged. The degree bound is proved through monomial expansion and finite product bounds, and does not depend on u,K or polynomial coefficients. Noninvertible substitutions are included; lattice sampling still separately requires positive integer K and coprime rough steps.',
    'The transformed coordinate polynomial is explicitly obtained by substituting in the previously constructed original native log Q polynomial. Its equality holds jointly for all real z,y. This does not prove stretched-filtration polynomiality or the analytic sampling estimates.',
    'All retained proof files and transitive axiom sets are unchanged; these are author-side checks, not independent kernel replay.',
]
source = source[:a] + 'application_review=COMPONENTS+' + repr(review) + '+[REMAINING],\n        ' + source[b:]
source = re.sub("reference_scope='[^']*'", "reference_scope='06_rough_progressions rough-kernel-test and affine kernel spatial substitution'", source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print('Prepared audit for', len(modules), 'modules.')
