from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-localized-intersection-density-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-localized-intersection-density-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-localized-intersection-density'", "PREFIX = 'round-joint-localization'")
source = source.replace("OLD = 'round-localized-dual-span'", "OLD = 'round-localized-intersection-density'")
modules = ['Hindman168/JointMixedDualSpan.lean', 'Hindman168/JointMixedDualProducts.lean',
           'Hindman168/JointMixedDualDensity.lean']
components = [
    'The first-direction actual dual generators may now be required to have all nonroot unit inputs represented in both original factors. Their closed Hilbert span is defined and proved equal to the original factor intersection. Joint input structure survives finite products and translations selected separately by input, stage and original cell. Exact finite products of these actual dual generators lie in their joint closed span, and every actual unit represented member multiplies that span into itself. Unit-interval projection representatives, orthogonal residual separation and projection continuity prove the full completed-Hilbert-space density equality. Every intersection vector has actual uniformly bounded approximants in the original algebraic span of joint dual families, with all original cell weights retained. The same statement can be applied with the two factors interchanged.'
]
old_gap = ' Localization inside the intersection itself, supplying actual inputs retaining both original factors for the two-level concatenation recursion, still needs to be integrated.'
assert old_gap in previous.REMAINING
remaining = previous.REMAINING.replace(old_gap,
    ' ' + components[0] + ' The two-level approximation and nested recursive coefficient expansions still need to be connected to the higher-order concatenation induction.')
source = re.sub(r'^MODULES = .*$', 'MODULES = ' + repr(modules), source, flags=re.M)
source = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), source, flags=re.M)
source = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), source, flags=re.M)
counts = {'1113': '1115', '1097': '1100', '5191': '5211', '1115': '1118', '1106': '1109'}
source = re.sub(r'\b(?:1113|1097|5191|1115|1106)\b', lambda m: counts[m.group()], source)
source = source.replace('assert len(names) == len(set(names)) == 10', 'assert len(names) == len(set(names)) == 20')
source = source.replace('for kind, _ in values) == 10', 'for kind, _ in values) == 16')
source = source.replace("'theorem_count': 10", "'theorem_count': 16")
source = source.replace('and len(names) == 10', 'and len(names) == 20')
for old_text, new_text in [
    ('new_theorems=10', 'new_theorems=16'), ('new_definitions=0', 'new_definitions=3'),
    ('new_instances=0', 'new_instances=1'), ('new_axiom_reports=10', 'new_axiom_reports=20'),
    ('new_module_count=2', 'new_module_count=3'), ('new_theorem_count=10', 'new_theorem_count=16'),
    ('new_selected_report_count=10', 'new_selected_report_count=20')
]:
    source = source.replace(old_text, new_text)
review = [
    'PROGRESS. The localized-intersection-density round was rechecked before edits. Retained proof source hashes and axiom sets remain unchanged.',
    'The new generators are actual first-direction mixed duals with nonroot unit inputs represented in the intersection of both original factors. This joint input condition is explicit and is stronger than the preceding localized-family condition. The unused root is normalized using the previously proved exact nonroot congruence.',
    'Joint families are shown to be a subset of the earlier localized families. Their closed Hilbert span therefore lies in the original factor intersection when the second degree is positive. The actual constant-one family is supplied with explicit membership in both factors, so it belongs to the joint span as well.',
    'The shifted-product helper proves membership separately in both original factors, using their previously verified positive-degree unit multiplication and translation closure. Shifts may vary by input, stage and original cell. No pointwise structure or invariance is assumed in place of actual Hilbert factor membership.',
    'The exact averaged dual identity for finite products is applied with its original subgroup Haar law. For every selected internal shift array, the new inputs are unit and remain in both factors by the shifted-product helper. Each selected dual is a genuine joint generator, so the internal-average theorem places the actual finite product in the joint closed span without a bounded-cardinality assumption.',
    'Pairwise joint generator closure is discharged by the finite-product theorem. The generic unit-generated-algebra theorem then proves that every actual unit represented member of the joint closed span multiplies it into itself. Both positive degrees are displayed where the two factor multiplication closures are used.',
    'For an actual unit represented member of the original intersection orthogonal to the joint span, its own first-direction pure dual has joint inputs and is a joint generator. The exact weighted correlation-power identity gives a vanishing first Gowers moment and seminorm, hence orthogonality to the whole first factor.',
    'The previously audited generic algebra projection theorem is applied with its one and unit-product premises discharged. For a unit-interval actual intersection member, its residual after the joint projection remains in both factors and is unit bounded. The new separation theorem makes this residual orthogonal to the first factor, so its Hilbert norm is zero.',
    'Projection continuity extends the argument to all completed Hilbert vectors by using bounded first-factor generators and the second-factor projection. This proves the full joint-span/intersection equality. The approximation corollary supplies actual members of the original joint-family algebraic span with arbitrary Hilbert error and a pointwise bound that may depend on the approximation.',
    'The specialization scripts only read retained proof sources. The stronger membership conditions, both-degree requirements, changed selected-input proof, joint pure-dual separation premise and residual intersection membership are written to new modules and individually compiled. No retained theorem is changed or assumed stronger than its audited statement.',
    'This matches the Section 7 requirement that the first dual inputs, and subsequently the second dual inputs obtained by swapping the factors, retain both original factors. Multilinear continuity for inserting finite dual approximations and the actual two-level recursive expansion still need to be integrated; no higher-order concatenation containment is claimed.',
    'Sixteen theorems, three definitions and one projection instance are audited. Joint actual generator-density is now proved. Full higher-order concatenation, qualitative Bessel and the original StrongConjecture remain unproved.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://arxiv.org/html/1603.07815v4', reference_scope='Section 7 joint input localization')\n"
) + source[end:]
Path('round-joint-localization-audit.py').write_text(source, encoding='utf-8')
print('Prepared three-module audit: sixteen theorems, three definitions, one instance.')
