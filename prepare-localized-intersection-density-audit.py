from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-localized-dual-span-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-localized-dual-span-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-localized-dual-span'", "PREFIX = 'round-localized-intersection-density'")
source = source.replace("OLD = 'round-pair-gowers-testing'", "OLD = 'round-localized-dual-span'")
modules = ['Hindman168/WeightedHaarAlgebraProjection.lean', 'Hindman168/LocalizedMixedDualDensity.lean']
components = [
    'A closed unit multiplier algebra containing the constant one now has actual power and polynomial representatives for uniformly bounded represented members, continuous functional calculus for such representatives, unit-interval approximants of its actual orthogonal projection, and an exact unit-interval projection representative for tail-containing ultrafilters. These results are discharged for the previously constructed localized dual span. Unit-interval actual members of the original factor intersection belong to that localized span: their residual after the localized projection remains in both original factors, and the localized separation theorem makes that residual orthogonal to the first factor, so it vanishes. Projection continuity extends this argument from bounded first-factor generators to the entire completed Hilbert space. Consequently the actual localized dual span is proved equal to the original factor intersection, with actual uniformly bounded algebraic-span approximants and unchanged cell weights.'
]
old_gap = ' The reverse inclusion identifying the localized span with the intersection remains to be proved; it still requires the clipping and bounded-projection argument for this new space.'
assert old_gap in previous.REMAINING
remaining = previous.REMAINING.replace(old_gap,
    ' ' + components[0] + ' Localization inside the intersection itself, supplying actual inputs retaining both original factors for the two-level concatenation recursion, still needs to be integrated.')
source = re.sub(r'^MODULES = .*$', 'MODULES = ' + repr(modules), source, flags=re.M)
source = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), source, flags=re.M)
source = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), source, flags=re.M)
counts = {'1110': '1113', '1095': '1097', '5181': '5191', '1113': '1115', '1104': '1106'}
source = re.sub(r'\b(?:1110|1095|5181|1113|1104)\b', lambda m: counts[m.group()], source)
source = source.replace('assert len(names) == len(set(names)) == 18', 'assert len(names) == len(set(names)) == 10')
source = source.replace('for kind, _ in values) == 14', 'for kind, _ in values) == 10')
source = source.replace("'theorem_count': 14", "'theorem_count': 10")
source = source.replace('and len(names) == 18', 'and len(names) == 10')
for old_text, new_text in [
    ('new_theorems=14', 'new_theorems=10'), ('new_definitions=3', 'new_definitions=0'),
    ('new_instances=1', 'new_instances=0'), ('new_axiom_reports=18', 'new_axiom_reports=10'),
    ('new_module_count=3', 'new_module_count=2'), ('new_theorem_count=14', 'new_theorem_count=10'),
    ('new_selected_report_count=18', 'new_selected_report_count=10')
]:
    source = source.replace(old_text, new_text)
review = [
    'PROGRESS. The localized-dual-span round was rechecked before edits. Retained proof source hashes and axiom sets remain unchanged.',
    'The generic algebra theorem explicitly assumes membership of the actual constant-one family and closure under each actual unit represented multiplier. These premises are not assumptions standing in for the desired localization: both are discharged by the previously audited localized-space theorems in the application.',
    'For an actual represented member with pointwise bound B, normalization by B+1 yields an actual unit multiplier in the same space. Powers are constructed with pointwise bound B^n. Their membership follows inductively from unit multiplication and scalar closure. Polynomial representatives are actual finite linear combinations of these powers.',
    'Continuous compositions are approximated on the fixed compact interval [-B,B] by real polynomials. The verified weighted Haar uniform distance bound and closedness give membership of the actual composition. No uniform B across all approximations is claimed.',
    'The generic generated-span approximation supplies a uniformly bounded actual representative near the genuine projection. Its unit-interval clip remains in the same space, and the previously proved projection-clipping distance inequality preserves the approximation error. This gives actual unit-interval projection approximants.',
    'The exact projection representative uses the already verified bounded diagonal theorem with reciprocal errors. The tail-containing-ultrafilter hypothesis is explicit. Pointwise interval bounds survive selection, and no countable intersection of large sets is assumed.',
    'For a unit-interval actual function already in the original intersection, subtracting the actual localized projection leaves a unit residual. Since the localized span is contained in the intersection, this residual remains in both factors. It is orthogonal to the localized span by the genuine projection property, so the audited localized separation theorem makes it orthogonal to the first factor. Membership in that factor forces its Hilbert norm to zero.',
    'To extend beyond represented unit inputs, first-factor hull generators are shifted and rescaled to [0,1]. Their second-factor projection has an exact unit-interval representative and remains in the first factor by the previously proved projection-preservation theorem. The unit-intersection argument places it in the localized span. Projection continuity and closedness extend the inclusion from the generator span to the entire first factor.',
    'Every completed Hilbert vector in the original intersection is fixed by the second projection. This proves the reverse inclusion and the exact localized-span/intersection equality. The explicit approximation corollary returns an actual member of the original localized-family algebraic span with a pointwise uniform bound and arbitrarily small Hilbert error.',
    'The primary Tao-Ziegler reference was reread at Corollary 6.4 and Section 7. The proved equality localizes the first dual construction to the second factor. Section 7 also localizes inside the intersection itself, with inputs retaining both factors, before its two-level recursion. That stronger input integration and the higher-order concatenation conclusion are not asserted by the current equality.',
    'Ten theorems are audited. The localized generator-density equality is now proved under the displayed positive degrees, normalized nonnegative cell weights and tail-containing-ultrafilter hypothesis. Full higher-order concatenation, qualitative Bessel and the original StrongConjecture remain unproved.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://arxiv.org/html/1603.07815v4', reference_scope='Corollary 6.4 and Section 7')\n"
) + source[end:]
Path('round-localized-intersection-density-audit.py').write_text(source, encoding='utf-8')
print('Prepared two-module audit for ten localization and projection theorems.')
