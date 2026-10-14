from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-weighted-bessel-sampling-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-weighted-bessel-sampling-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-weighted-bessel-sampling'", "PREFIX = 'round-uniform-bessel-modulus'")
source = source.replace("OLD = 'round-finite-bessel'", "OLD = 'round-weighted-bessel-sampling'")
modules = ['Hindman168/FiniteWeightedSubgroupSystem.lean',
           'Hindman168/FiniteWeightedBesselThreshold.lean',
           'Hindman168/FiniteWeightedBesselModulus.lean',
           'Hindman168/WeightedSubgroupQualitativeBessel.lean',
           'Hindman168/FiniteMassWeightedSubgroupBessel.lean',
           'Hindman168/MasterQualitativeSubgroupBessel.lean',
           'Hindman168/MasterActualCellBessel.lean']
components = ['The arbitrary weighted varying-index Bessel limit now yields one positive finite threshold uniformly over every finite subgroup weighted Haar system, including changing group laws, all finite sizes, direction families, real weights and unit inputs. A supremum over all ordinary small-type finite systems defines one nondecreasing modulus in [0,1] tending to zero as the pair budget tends to zero. The direct original weighted local mean is bounded by this modulus of the original independent pair mean at order 2d-1. Restricting an arbitrary finite mass to its actual support preserves every original coefficient and extends the bound to infinite ambient index types. For the original constructed master good-tuple law, rough coprimality and this proved modulus give a positive global Gowers threshold that eventually controls the mean of local subgroup norms, uniformly over the cyclic modulus, original cell probabilities and all unit inputs. The exact original harmonic cell probabilities and common cyclic order instantiate this estimate for actual integer inputs and polynomial subgroup directions. No Bessel theorem is assumed as a hypothesis.']
gap = 'The varying-index weighted Bessel limit still needs a uniform finite threshold over all finite systems. The full qualitative Bessel modulus, remaining replica integration, cyclic-to-interval transfer and inverse correlator existence remain missing.'
assert gap in previous.REMAINING
remaining = previous.REMAINING.replace(gap, components[0] +
    ' The finite-subgroup weighted Haar qualitative Bessel modulus and its actual harmonic-cell master good-tuple application are proved. Remaining short-cube and replica integration, cyclic-to-interval transfer and inverse correlator existence remain missing.')
for field, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + field + r' = .*$', field + ' = ' + repr(value), source, flags=re.M)
counts = {'1138': '1142', '1124': '1131', '5281': '5319', '1142': '1149', '1133': '1140'}
source = re.sub(r'\b(?:1138|1124|5281|1142|1133)\b', lambda m: counts[m.group()], source)
source = source.replace("('Hindman168.FiniteMass.' if p in MODULES[:2] else 'Hindman168.')", "'Hindman168.'")
source = source.replace('== len(set(names)) == 10', '== len(set(names)) == 38')
source = source.replace("for kind, _ in values) == 10", "for kind, _ in values) == 16")
source = source.replace("'theorem_count': 10", "'theorem_count': 16, 'selected_report_count': 38")
source = source.replace("len(names) == 10", "len(names) == 38")
for a, b in [('new_theorems=10', 'new_theorems=16'),
             ('new_definitions=0', 'new_definitions=4'),
             ('new_instances=0', 'new_instances=4'),
             ('new_axiom_reports=10', 'new_axiom_reports=38'),
             ('new_module_count=4', 'new_module_count=7'),
             ('new_theorem_count=10', 'new_theorem_count=16'),
             ('new_selected_report_count=10', 'new_selected_report_count=38')]:
    source = source.replace(a, b)
fields = ['G', 'addCommGroup', 'finiteGroup', 'κ', 'finiteCells', 'A', 'finiteIndices',
          'p', 'p_nonneg', 'p_total', 'α', 'α_nonneg', 'α_total', 'Q', 'g', 'g_unit']
start = source.index('def declarations():')
end = source.index('\n\ndef register():', start)
source = source[:start] + (
    'STRUCTURE_FIELDS = ' + repr(fields) + '\n\n'
    'def declarations():\n'
    "    ds = {p: re.findall(r'^\\s*(?:noncomputable\\s+)?(theorem|lemma|def|abbrev|instance)\\s+([A-Za-z][A-Za-z0-9_\\.]*)', old.lean_code(read(p)), re.M) for p in MODULES}\n"
    "    code = old.lean_code(read(MODULES[0]))\n"
    "    assert re.findall(r'^structure (\\w+)', code, re.M) == ['FiniteWeightedSubgroupSystem']\n"
    "    assert re.findall(r'^  ([^\\s:]+) :', code, re.M) == STRUCTURE_FIELDS\n"
    "    assert re.findall(r'FiniteWeightedSubgroupSystem\\.(\\w+)', code) == ['addCommGroup', 'finiteGroup', 'finiteCells', 'finiteIndices']\n"
    "    generated = [('structure', 'FiniteWeightedSubgroupSystem'), ('constructor', 'FiniteWeightedSubgroupSystem.mk')]\n"
    "    generated += [('projection', 'FiniteWeightedSubgroupSystem.' + f) for f in STRUCTURE_FIELDS]\n"
    '    ds[MODULES[0]] = generated + ds[MODULES[0]]\n'
    '    return ds\n'
) + source[end:]
source = source.replace('new_axiom_reports=38, standard_axioms_only=True,',
    'new_axiom_reports=38, new_structures=1, new_constructors=1, new_projections=16, standard_axioms_only=True,')
review = [
    'PROGRESS. The weighted sampling audit was rechecked before edits, and its manifest was saved as the baseline. All retained proof-source hashes and previous selected axiom sets remain unchanged. Only root imports and the selected kernel registry change among retained files.',
    'The bundled finite system contains the actual group type and law, actual finite cell and direction types, both original nonnegative normalized real laws, actual subgroups and an actual unit input. Its constructor and all sixteen fields are explicitly registered in the selected kernel audit. Four fields are registered as typeclass instances. There are no cardinality bounds or placeholders for proof steps.',
    'The null-limit implication is applied to every sequence of these systems by constructing the original weighted Haar unit family with the supplied cell law. If no uniform positive threshold exists, select for each natural n a complete actual system with pair mean at most 1/(n+1) and local mean at least epsilon. The nonnegative pair means tend to zero along the natural hyperfilter, while the proved Bessel limit forces the local means to zero, a contradiction. No fixed group, direction family or cell count is retained across the selected sequence.',
    'The modulus is the supremum of zero and all achievable local means within the pair budget, over all ordinary small-type finite systems. Unit input bounds place this set below one. Inclusion of zero makes it nonempty for every real budget, including negative budgets. Enlarging a pair budget enlarges this set, so its supremum is nondecreasing. The uniform threshold at epsilon/2 bounds the entire set by epsilon/2, proving the modulus tends to zero. The direct local-mean bound is an actual supremum-membership inequality, not a premise asserting a universal Bessel bound.',
    'The support conversion uses the exact finite sum over the original finite mass support and its original coefficients. The tensor law is identified with the original nested expectation. Infinite ambient types such as natural prime tuples therefore require no Fintype instance and no rational approximation or replacement probability law.',
    'The master application uses the original conditioned dyadic prime-tuple mass. Its positive event limit supplies normalization. Rough coprimality bounds the independent pair mean by the actual global Gowers value plus a vanishing error. Choose both global threshold and eventual rough error at half the universal pair budget. The proved modulus then controls the original local mean eventually, uniformly over cyclic modulus, original finite cell law and every actual unit input. No Bessel theorem is supplied as a premise.',
    'The actual-cell interface instantiates the generic master estimate with the original common cyclic order R/M and the exact normalized harmonic cell probabilities already proved in the retained sources. Its function is the actual integer input pulled back to each original residue cell. Polynomial subgroup directions and conditioned original prime tuples are unchanged. This is the finite-subgroup weighted Haar specialization required by the current master estimates; it does not assert a theorem for every abstract probability action or finish the original prediction inverse lemma. The remaining master short-cube, replica and cyclic-to-interval integrations, inverse correlator existence, final calibration and monochromatic extraction remain missing. StrongConjecture is unchanged and unproved.',
    'Development failures and warnings are not validation evidence. The deprecated negation tactic was replaced by push Not. Explicit support-sum functions repaired an elaboration failure. One universe is used for the bundle to avoid a redundant-universe linter warning; the named modulus covers all ordinary small-type finite systems required by the master interface. No set_option or raised resource bounds are used. Only terminal warning-free focused compilations, the full build and the complete selected kernel output count as validation.',
    'Seven modules contain sixteen proved theorems, four definitions, one structure and its constructor and sixteen projections, including four registered instance projections. All thirty-eight new selected declarations are individually checked for their transitive axioms. No unavoidable blocker is established; publication, PR and award claim remain pending the complete original proof.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://arxiv.org/html/1603.07815v4', reference_scope='Theorem 1.23 finite-subgroup case and Section 8 compactness; OpenAI prediction-bessel equation and combining subgroups paragraph')\n"
) + source[end:]
Path('round-uniform-bessel-modulus-audit.py').write_text(source, encoding='utf-8')
print('Prepared seven-module audit: sixteen theorems, thirty-eight selected declarations.')
