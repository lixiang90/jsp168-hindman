from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-master-short-bessel-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-weighted-bessel-sampling-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-weighted-bessel-sampling'", "PREFIX = 'round-interval-cube-geometry'")
source = source.replace("OLD = 'round-finite-bessel'", "OLD = 'round-master-short-bessel'")
modules = ['Hindman168/IntegerCubeCornerCoordinates.lean',
           'Hindman168/IntegerIntervalCubeDomain.lean',
           'Hindman168/IntegerIntervalCubeCardBounds.lean',
           'Hindman168/IntegerPeriodicCubeAverage.lean',
           'Hindman168/IntegerIntervalCubeTranslateBoundary.lean',
           'Hindman168/IntegerCubeResidueShiftBounds.lean']
components = ['The actual signed-increment integer interval cube domain is now a finite set with exact membership equivalent to every vertex lying in [0,L). A chosen vertex and its d adjacent vertices determine the original integer cube parameters injectively. Hence a vertex strip [a,b) contains at most (b-a).toNat times L^d actual domain parameters. Every nonnegative root/increment box of width H with (d+1)H <= L lies in the full domain, giving cardinality at least H^(d+1). A nonnegative parameter translate moving every vertex by at most D has at most 2^d D L^d original cubes leaving the domain, and the backward translate has the same bound from lower strips. Averaging canonical residue-parameter shifts gives exactly the full cyclic subgroup cube mean at every original integer parameter point. Each such shift moves every vertex by a nonnegative amount at most (d+1)(q-1). No cyclic modulus or interval length is fixed in these results.']
gap = 'Remaining replica integration, cyclic-to-interval transfer and inverse correlator existence remain missing.'
assert gap in previous.REMAINING
remaining = previous.REMAINING.replace(gap, components[0] +
    ' The normalized cyclic-to-interval error bound and inverse correlator transfer, remaining replica integration and inverse correlator existence remain missing.')
for field, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + field + r' = .*$', field + ' = ' + repr(value), source, flags=re.M)
counts = {'1138': '1153', '1124': '1141', '5281': '5341', '1142': '1159', '1133': '1150'}
source = re.sub(r'\b(?:1138|1124|5281|1142|1133)\b', lambda m: counts[m.group()], source)
source = source.replace("('Hindman168.FiniteMass.' if p in MODULES[:2] else 'Hindman168.')", "'Hindman168.'")
source = source.replace('== len(set(names)) == 10', '== len(set(names)) == 18')
source = source.replace("for kind, _ in values) == 10", "for kind, _ in values) == 13")
source = source.replace("'theorem_count': 10", "'theorem_count': 13, 'selected_report_count': 18")
source = source.replace("len(names) == 10", "len(names) == 18")
for a, b in [('new_theorems=10', 'new_theorems=13'),
             ('new_definitions=0', 'new_definitions=5'),
             ('new_axiom_reports=10', 'new_axiom_reports=18'),
             ('new_module_count=4', 'new_module_count=6'),
             ('new_theorem_count=10', 'new_theorem_count=13'),
             ('new_selected_report_count=10', 'new_selected_report_count=18')]:
    source = source.replace(a, b)
source = source.replace("| {'Hindman168.intervalResidueParent', 'Hindman168.completeResidueCellPoint'}",
    "| {'Hindman168.intervalResidueParent', 'Hindman168.completeResidueCellPoint', 'Hindman168.integerCubeResidueShift'}")
review = [
    'PROGRESS. The original short-cube Bessel round was rechecked before edits, and its exact manifest was saved as the baseline. All retained proof-source hashes, selected kernel reports, dependency pins and manuscript hashes remain unchanged. Only root imports and the selected kernel registry change among retained files.',
    'The integer cube uses a signed integer root and d signed integer increments. Its finite interval domain filters a bounding box by all vertex interval conditions. The reverse membership implication proves that any integer cube with all vertices in [0,L) already belongs to that box: the empty vertex bounds the root and each singleton bounds its increment by subtraction. Thus no positive-increment restriction changes the actual domain.',
    'The existing cube reflection identity gives the exact adjacent-corner formula. Equality of a selected corner value and each adjacent vertex yields equality of every increment, followed by equality of the original root. The coordinate map is injective for all dimensions, including dimension zero.',
    'The injective corner-coordinate map sends a chosen-vertex strip into [a,b) times d copies of [0,L). Exact finite product and integer interval cardinalities give strip count at most (b-a).toNat * L^d. For the lower estimate, the root and every increment in [0,H) have nonnegative vertices and each vertex is strictly below (d+1)H. When this is at most L, that actual parameter box lies in the full signed-increment domain and has H^(d+1) points. This box is only a lower-count subset, not a replacement integration domain.',
    'For a parameter translation with every vertex displacement in [0,D], a translated original domain cube cannot fail a lower vertex bound; any failure occurs at an upper vertex, so an original vertex lies in [L-D,L). The union over all 2^d vertices and the strip bound give 2^d D L^d departing cubes. For the backward translation no upper bound can fail; a failing vertex puts an original vertex in [0,D). The same union and strip argument prove the other boundary-side count. Both sides are proved independently; neither is silently omitted.',
    'The actual periodic cube product is evaluated by reducing each original integer vertex modulo the actual cyclic q. Canonical residue shifts lift the finite root and increment residues to integer representatives. Integer-cast and sum identities show that every translated product is exactly the cyclic cube product on one translated finite parameter tuple. Finite Haar translation invariance removes that tuple shift. The top-subgroup direction equivalence identifies the finite parameter mean with the actual full cyclic subgroup cube mean. This is an exact pointwise average identity for every integer parameter point, not an approximate equidistribution assumption.',
    'Every canonical shift coordinate is between zero and q-1. At a vertex, nonnegative increment sums and the finite vertex-cardinality bound give displacement at most (d+1)(q-1), uniformly in all vertices and all residue tuples. This supplies the concrete bounded nonnegative translations needed by the proved boundary counts.',
    'Development failures and warnings are excluded from validation evidence. Explicit Equiv function coercion repaired the reflection elaboration. Finset.product_eq_sprod exposes the current finite-product cardinality API. Explicit integer and natural casts repaired finite-sum type inference. No set_option or increased resource bound occurs in new sources. Only terminal successful warning-free focused compilations, the full build and complete selected kernel output count as verification.',
    'Six modules contain thirteen proved theorems and five definitions; all eighteen new declarations are selected for transitive axiom audit. The pure canonical residue-shift definition is separately checked axiom-free, and the fourteen retained axiom-free declarations remain unchanged. The normalized sum discrepancy and O_d(1/K) cyclic-to-interval power estimate still need integration of these exact geometric ingredients. Inverse correlator existence, replica integration, final calibration and original monochromatic extraction remain missing. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize claim remain pending.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='05_prediction: From the global norm to a nilsequence projection; exact integer cube domain, vertex-neighbor boundary counts and parameter residue averaging')\n"
) + source[end:]
Path('round-interval-cube-geometry-audit.py').write_text(source, encoding='utf-8')
print('Prepared six-module audit: thirteen theorems, five definitions.')
