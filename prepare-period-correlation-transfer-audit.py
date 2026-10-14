from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-cyclic-interval-powers-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-cyclic-interval-powers-audit.py').read_text(encoding='utf-8')
source = source.replace('"""Register and audit the actual cyclic-to-interval power and positive-norm transfer."""',
    '"""Register and audit exact period correlation extraction and native integer-cell rebasing."""')
source = source.replace("PREFIX = 'round-cyclic-interval-powers'", "PREFIX = 'round-period-correlation-transfer'")
source = source.replace("OLD = 'round-interval-cube-geometry'", "OLD = 'round-cyclic-interval-powers'")
modules = ['Hindman168/FiniteComplexMean.lean',
           'Hindman168/PeriodicComplexCorrelation.lean',
           'Hindman168/NilsequencePeriodCorrelation.lean',
           'Hindman168/PhaseObservableCorrelation.lean',
           'Hindman168/NativeRealPeriodCorrelation.lean',
           'Hindman168/CompleteCellNilOrbitRebase.lean',
           'Hindman168/NativeCellCorrelationTransfer.lean']
components = ['Exact normalized complex finite means now have equivalence and product identities and a norm bound by the original real mean of norms. A finite nonempty complex mean has some original summand with at least its modulus. The exact finite product-coordinate equivalence decomposes the mean on Kq integer representatives into K actual consecutive period means. For a periodic cyclic input and an arbitrary, possibly nonperiodic correlator, one actual period retains the entire original correlation threshold without a phase-agreement premise. On the original native nilmanifold the period translate changes only the basepoint to g^(jq)x; the manifold, lattice, step bound, metric, translating element and original complex observable are retained literally. Unit-phase rotation followed by real part defines an actual continuous real observable with the same supremum bound and Lipschitz constant. One selected unit phase makes its real correlation equal the original complex correlation modulus exactly. The resulting native real period correlator retains the threshold and all displayed bounds. For the original integer residue-cell points y=kMq+r+Mt, exact Euclidean division gives y/M=kq+t for every integer k. Rebasing the local orbit by g^(-kq) therefore gives exactly the existing globally anchored pieceLinearOrbit, and the actual cell Haar correlation is unchanged. Combining period selection, unit-phase real conversion and this rebasing transports a bounded native correlator on K periodic copies of an actual integer residue cell to that original cell and the retained globally anchored piece orbit. No inverse theorem or existence of such a correlator is assumed as an axiom or proved by these transport results.']
gap = 'Period correlation extraction and inverse correlator transfer, remaining replica integration and inverse correlator existence remain missing.'
assert gap in previous.REMAINING
remaining = previous.REMAINING.replace(gap, components[0] +
    ' Inverse correlator existence and its quantitative finite-list application to the fine projection, and remaining replica integration remain missing.')
for field, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + field + r' = .*$', field + ' = ' + repr(value), source, flags=re.M)
counts = {'1159': '1165', '1147': '1154', '5360': '5384', '1165': '1172', '1156': '1163'}
source = re.sub(r'\b(?:1159|1147|5360|1165|1156)\b', lambda m: counts[m.group()], source)
source = source.replace('== len(set(names)) == 19', '== len(set(names)) == 24')
source = source.replace("'selected_report_count': 19", "'selected_report_count': 24")
source = source.replace('len(names) == 19', 'len(names) == 24')
source = source.replace("for kind, _ in values) == 16", "for kind, _ in values) == 22")
source = source.replace("'theorem_count': 16", "'theorem_count': 22")
source = source.replace('new_theorems=16', 'new_theorems=22')
source = source.replace('new_theorem_count=16', 'new_theorem_count=22')
source = source.replace('new_definitions=3', 'new_definitions=2')
source = source.replace('new_axiom_reports=19', 'new_axiom_reports=24')
source = source.replace('new_module_count=6', 'new_module_count=7')
source = source.replace('new_selected_report_count=19', 'new_selected_report_count=24')
review = [
    'PROGRESS. The preceding exact cyclic-to-interval power and positive norm transfer round was rechecked terminal-successfully before edits. Its authoritative manifest was copied unchanged to this saved baseline. Retained proof-source hashes and selected kernel axiom sets remain unchanged; only root imports and the kernel declaration registry change among retained files.',
    'The complex normalized mean is the exact sum divided by the original finite type cardinality. Equivalence reindexing preserves it, and the finite product mean is the iterated mean. Its norm is at most the original normalized real sum of individual norms. A maximum among an actual nonempty finite family supplies one actual value at least as large as the complex mean modulus. This proves selection without replacing the original period weights or assuming all correlations have one phase.',
    'The original finite product-coordinate equivalence sends (j,z) to z+q*j in Fin(Kq). Commutative natural arithmetic identifies this with j*q+z. Thus the full representative mean splits exactly into K original q-term period means. In each period, reduction of j*q+z modulo q equals the original cyclic representative z. The correlator remains an arbitrary function on natural indices and need not have period q. One selected period retains the given modulus threshold with no quantitative loss.',
    'For an arbitrary group, zpow_add and associativity give the quotient orbit shift identity: g^(n+t)x = g^n(g^t x). No commutativity of the entire group is assumed. The selected period j therefore uses the original observable and translating element and basepoint g^(jq)x. Its native corollary retains the exact NativeNilmanifoldData object D, including the original finite-dimensional model, connected simply connected Lie group, lattice, compact quotient, metric and step bound. An inverse-theorem finite-list entry would therefore be unchanged by this operation.',
    'The phase-real observable is an actual continuous map, given by the real part of eta times the original complex observable. For a unit eta, absolute real part is bounded by the complex norm, so every original supremum bound remains valid. The distance proof uses real-part contraction and the exact norm of unit multiplication, so the same original Lipschitz constant remains valid, not a larger or data-dependent constant.',
    'Complex finite averaging commutes exactly with real part and multiplication by a constant. For real input v, this gives real mean(v*Re(eta*psi)) = Re(eta*complex mean(v*psi)). The existing proved complex unit-phase lemma selects eta such that eta times that actual mean is its nonnegative norm. Thus the resulting real correlation equals the original complex modulus exactly, including when the original mean is zero. The native real period theorem combines this selection with the exact period basepoint and retains all original observable bounds.',
    'For every integer cell index k, positive M, residue r in Fin M and original t in Fin q, y=kMq+r+Mt can be rewritten as r+M(kq+t). The residue lies in [0,M), so exact Euclidean division gives y/M=kq+t even when k is negative. The original piece exponent therefore represents the local cyclic orbit after rebasing its basepoint by g^(-kq). The adjacent powers of the same group element cancel using zpow_add, without an ambient commutativity assumption. The retained actual complete-cell points and original finite Haar mean are used; neither the integer parameter nor its law is replaced.',
    'The final native complete-cell transport instantiates the cyclic input with the actual integer function evaluated at kMq+r+M*z.val. For t in Fin q, the actual ZMod representative identity recovers the original completeResidueCellPoint exactly. Period selection, unit-phase real conversion and integer-cell rebasing then give the globally anchored pieceLinearOrbit with basepoint g^(-kq)(g^(jq)x), on the same D and with the same real observable bounds. Its correlation retains the displayed threshold on the original cell average.',
    'Development failures and warnings are excluded from evidence. Natural product commutation was proved by ac_rfl rather than a linear arithmetic tactic. The period reindexing function was supplied explicitly. A missing named universe was discovered by the project build with autoImplicit=false and repaired; subsequent focused checks for the dependent native and cell modules use that actual project setting. Unit-phase continuity uses explicit composition with continuous_re; NNReal notation is opened explicitly. The integer division rewrite uses the exact product order of Int.add_mul_ediv_left. No set_option or increased resource limit occurs in new sources. Only terminal warning-free focused checks, complete build and full selected kernel output count as verification.',
    'Seven modules contain twenty-two proved theorems and two definitions; all twenty-four new declarations are selected for transitive axiom audit. The fifteen retained axiom-free declarations remain unchanged. These are exact correlator transport theorems with an explicit actual-correlation input; they do not construct the missing inverse correlator or insert an unproved inverse theorem as an axiom. The positive norm transfer is already retained, but inverse correlator existence, its quantitative finite-list fine-projection application, replica integration, calibration and final original monochromatic extraction remain missing. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize claim remain pending.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='05_prediction: exact one-period correlation extraction, original nilsequence basepoint translation, real observable conversion and native original integer-cell rebasing')\n"
) + source[end:]
Path('round-period-correlation-transfer-audit.py').write_text(source, encoding='utf-8')
print('Prepared seven-module audit: twenty-two theorems, two definitions.')
