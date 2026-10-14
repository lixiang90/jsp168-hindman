from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-pair-gowers-testing-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-pair-gowers-testing-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-pair-gowers-testing'", "PREFIX = 'round-localized-dual-span'")
source = source.replace("OLD = 'round-uniform-gowers-threshold'", "OLD = 'round-pair-gowers-testing'")
modules = ['Hindman168/LocalizedMixedDualSpan.lean', 'Hindman168/WeightedHaarGeneratedAlgebra.lean',
           'Hindman168/LocalizedMixedDualProducts.lean']
components = [
    'The actual mixed-dual families with unit inputs represented in the other dual space now generate a defined closed Hilbert subspace. Root normalization is proved harmless. This localized span contains the constant one and is contained in the original factor intersection when the other degree is positive. Finite products of localized actual duals lie in the localized closed span by an exact averaged dual representation and the verified internal-average theorem. Generic unit-generated spans have uniformly bounded actual algebraic-span representatives and dense actual approximants. Unit multipliers whose products with the generators lie in the closed span preserve that span, and pairwise generator closure extends to every actual unit represented member. Consequently actual unit members of the localized span multiply it into itself. An actual unit represented member of the other factor orthogonal to this localized span has vanishing first-factor Gowers value and is orthogonal to the entire first factor.'
]
remaining = previous.REMAINING.replace(' Higher-order concatenation controlling dual correlations',
    ' ' + components[0] + ' The reverse inclusion identifying the localized span with the intersection remains to be proved; it still requires the clipping and bounded-projection argument for this new space. Higher-order concatenation controlling dual correlations')
source = re.sub(r'^MODULES = .*$', 'MODULES = ' + repr(modules), source, flags=re.M)
source = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), source, flags=re.M)
source = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), source, flags=re.M)
counts = {'1108': '1110', '1092': '1095', '5163': '5181', '1110': '1113', '1101': '1104'}
source = re.sub(r'\b(?:1108|1092|5163|1110|1101)\b', lambda m: counts[m.group()], source)
source = source.replace('assert len(names) == len(set(names)) == 7', 'assert len(names) == len(set(names)) == 18')
source = source.replace("for kind, _ in values) == 7", "for kind, _ in values) == 14")
source = source.replace("'theorem_count': 7", "'theorem_count': 14")
source = source.replace('and len(names) == 7', 'and len(names) == 18')
for old_text, new_text in [
    ('new_theorems=7', 'new_theorems=14'), ('new_definitions=0', 'new_definitions=3'),
    ('new_instances=0', 'new_instances=1'), ('new_axiom_reports=7', 'new_axiom_reports=18'),
    ('new_module_count=2', 'new_module_count=3'), ('new_theorem_count=7', 'new_theorem_count=14'),
    ('new_selected_report_count=7', 'new_selected_report_count=18')
]:
    source = source.replace(old_text, new_text)
review = [
    'PROGRESS. The pair-Gowers-testing round was rechecked before edits. Retained proof source hashes and axiom sets remain unchanged.',
    'The localized generators are actual mixed dual functions, not vectors assumed to possess localized representations. Their nonroot unit inputs have represented Hilbert images in the other closed dual space. The unused root may be set to zero, using an exact nonroot-congruence theorem, so requiring a unit root in the definition does not exclude the original unit-nonroot duals.',
    'The localized subspace is the topological closure of the actual generators span. An orthogonal-projection instance follows from closedness, and no representability or density property is inferred from this instance.',
    'The localized subspace contains the actual constant-one family. Generator containment in the first factor follows from the original cellwise mixed-dual hull, and containment in the positive-degree other factor follows from the actual internal-dual-closure theorem. Closedness of the intersection extends this containment to the whole localized space.',
    'Finite products use the verified exact averaged dual identity. For every selected internal shift array, the new input is a finite product of translated original inputs. Its unit bound and other-factor membership are proved. The selected dual is therefore a genuine localized generator, and the internal-average theorem preserves the original weighted Hilbert law without a bound on parameter cardinalities.',
    'For arbitrary sets of actual unit families, algebraic-span induction constructs an actual preimage in the original family span with one uniform pointwise bound. The bound may depend on the finite span expression and is not asserted uniform across approximations.',
    'The generic multiplier argument checks the algebraic generator span under the composed linear map, then extends through actual dense approximants and the already verified Hilbert distance contraction. Pairwise generator product closure extends first to generator multipliers on the whole space and then, by swapping the factors, to all actual unit represented multipliers in the space.',
    'For the localized generators, the required pairwise product premise is discharged by the actual finite-product theorem. Thus unit-product closure of the new localized space is proved, rather than inserted as a hypothesis.',
    'An actual unit member of the other factor orthogonal to the localized span is paired with its own first-direction pure dual, which is a localized generator. The exact correlation-power identity makes the first Gowers moment tend to zero, and the positive-degree root argument gives vanishing Gowers value and full first-factor orthogonality.',
    'Fourteen theorems, three definitions and one projection instance are audited. This constructs the localized space and proves its algebra and separation properties. The reverse inclusion from the original intersection is not claimed: clipping closure and bounded actual projection representatives for this localized space are still needed. Full higher-order concatenation, qualitative Bessel and the main StrongConjecture remain unproved.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING)\n'
) + source[end:]
Path('round-localized-dual-span-audit.py').write_text(source, encoding='utf-8')
print('Prepared three-module audit: fourteen theorems, three definitions, one instance.')
