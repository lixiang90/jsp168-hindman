from pathlib import Path
import ast
import json

PREFIX = 'round-native-rational-character-child-signal'
OLD = 'round-native-rational-frozen-child-signal'
MODULES = [
    'Hindman168/FiniteConditionedSignalBudgets.lean',
    'Hindman168/NativeRationalConstructedChildSignal.lean',
    'Hindman168/NativeRationalCharacterChildBudget.lean',
    'Hindman168/NativeRationalFiniteCharacterChildBudget.lean',
    'Hindman168/NativeRationalDenseChildSignal.lean',
    'Hindman168/NativeRationalDegreeTwoDenseChildSignal.lean',
    'Hindman168/NativeRationalChildScalarTransport.lean',
]
COMPONENTS = [
    'Genuine smaller-source child UNIT discrepancy now retains LITERAL affine polynomial construction, proved by constructing the source and comparing actual integer quotient samples. It is never inferred from quotient equality alone.',
    'All valid characters in the ACTUAL original finite Fourier character pool receive ONE positive UNIT signal threshold and ONE natural budget BEFORE every raw polynomial, denominator and sample length. The budget bounds true q/K/direction norm and analytic threshold; child length is at least N/B. Invalid characters and the empty pool are handled explicitly without false geometry.',
    'The actual dense ORIGINAL Fourier branch now yields full original horizontal/grid/monomial/binomial inverse OR a GENUINE constructed child source with strictly smaller natural nonlinearity, original-scale length and uniform UNIT discrepancy. Every original dense/table/right-factor property is retained. Degree two has no lower-degree inverse premise; general degree retains only the full lower-degree premise.',
    'Actual ALL-real right-ordered source factorization proves the ORIGINAL horizontal scalar polynomial identity. Literal affine child construction proves exact scalar affine composition. True positive exponential lattice powers prove integer horizontal values and clear EVERY rational-factor coefficient by the bounded natural multiplier M*q. These exact identities do not yet prove the full original coefficient transport bounds or same-degree induction.',
]
REMAINING = (
    'StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
    'The full original positive distinct rapidly separated monochromatic finite sums/products is the prize target. '
    'The original finite-character pool now has simultaneous genuine geometry/UNIT-signal budgets, '
    'and the dense native Fourier branches explicitly yield a constructed smaller-nonlinearity child source '
    'with uniform UNIT discrepancy and length>=N/B before all raw sources. '
    'Literal child affine source construction, original ALL-real horizontal scalar factor identity, '
    'and complete rational-factor coefficient integrality after M*q are proved. '
    'Remaining: quantitative affine translation/step/length/REAL-error transport to BOTH COMPLETE raw ORIGINAL '
    'coefficient tables, actual finite-child inverse budgeting, genuine well-founded degree+nonlinearity '
    'induction and all original small-N cases. P first/full diagonal alternative, corrected multivariate '
    'inverse, separate interval Gowers correlation inverse, rough progressions, cube/Alignment and final '
    'StrongConjecture remain OPEN. Fixed-data existential constants are distinct from explicit delta-power '
    'laws. Only true positive exponential lattice powers are used, not Exp(y) lattice membership. '
    'Author build/hash/axiom/source review is not independent kernel replay or external peer review. '
    'The repaired source slab estimate is not an unavoidable obstruction. Public repository/PR/prize '
    'milestone has not been reached.'
)

source = Path(OLD + '-audit.py').read_text(encoding='utf-8')
lines = source.splitlines(keepends=True)
replacements = dict(PREFIX=PREFIX, OLD=OLD, MODULES=MODULES, COMPONENTS=COMPONENTS, REMAINING=REMAINING)
for node in reversed(ast.parse(source).body):
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno] = [name + ' = ' + repr(replacements[name]) + '\n']
source = ''.join(lines)
source = source.replace('actual complex freezing, original-scale short residue progression and genuine smaller-filtration Unit-cube signal; full character-pool/source-coefficient induction and final target remain open',
                        'simultaneous original finite-character budgets, constructed child UNIT signal, exact horizontal scalar transport identities; quantitative coefficient transport, induction and final target remain open')
Path(PREFIX + '-audit.py').write_text(source, encoding='utf-8')
Path(PREFIX + '-mathematical-review.txt').write_text('''JSP-000168 mathematical/application review, 2026-10-13

Scope: Progress, not the full native inverse and not StrongConjecture.

1. Constructed child: The older child signal gives exact original INTEGER
quotient samples. The new source is literally affine-substituted pK, with
weights, degree and samples derived from the existing source constructor.
The two sources give equal finite discrepancy using the same observable.
No vector/group equality is deduced from quotient equality.

2. Character quantifiers: The true GOOD condition requires horizontal
integrality, zero actual commutator pairing and nonzero difference. Finite
choice assigns genuine geometry only under that condition. Dummy 1 budgets
on invalid members assert no geometry. Empty pools are covered. Sum bounds
and finite positive minimum are taken before M/p/N/F. Budget monotonicity
increases the analytic threshold and weakens child length/discrepancy.

3. Dense composition: Original Fourier packet supplies finite C, A/S and
threshold T0. Child budget B/theta is derived for that SAME pool and SAME
original Fourier signal. T=T0+B+1 supplies both thresholds. Existing original
inverse alternatives are retained; only the remaining true good-character
branch obtains the actual child. Degree-two lower-degree premise is discharged
by the registered genuine degree-one theorem. No same-degree inverse is used.

4. Original coefficient identities: Apply the horizontal logarithm character
to the actual ALL-real ordered product. Its proved additivity and exponential
inverse give exact scalar equality for every real x, hence polynomial equality.
Literal affine source gives scalar composition. Exp(y)^q in Gamma and actual
horizontal lattice integrality imply q*kappa(y) is integer. Clearing by M*q
makes EVERY rational-factor monomial coefficient integer, including the zero
outside-degree branch. Numerators may be unbounded; no smallness is asserted.

5. Remaining: Original quantitative coefficient bounds still require signed
translation, bounded progression powers, retained length scaling and actual
REAL-error estimates. Uniform child inverse constants across the finite
conjugate pool and genuine well-founded induction remain to be constructed.
These exact identities are not a conditional claim of the final theorem.

6. Source/award: Follow pinned OpenAI rough progression quantitative Leibman
route. The older slab counterexample refutes an intermediate displayed estimate,
not the proposition; its repair is retained and it is not a terminal obstruction.
Complete original proof is required for prize submission. No publication or
application milestone is asserted. This review is by the authoring agent;
build and axiom checks are not independent kernel replay or external review.
''', encoding='utf-8')
Path('openai-math-sync-2026-10-13.json').write_text(json.dumps(dict(
    checked_date='2026-10-13', repository='https://github.com/openai/math',
    method='Authenticated GitHub connector fetch_commit(main) and compare_commits',
    remote_main='1581d4cbdd69a0faf34b2089614fe2a814316a6a',
    previous_remote='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
    changed_files_since_previous=['.github/workflows/lock-prs.yml'],
    paper_reference_pin='adc7f1241b42e322a6451854ab7e4b4c146bf78a',
    conclusion='Only PR locking workflow changed since prior source inspection. Six proof sections separately rechecked against pinned local Git objects by round audit. No upstream proof compilation or independent mathematical verification asserted.'
), indent=2) + '\n', encoding='utf-8')
print(PREFIX)
