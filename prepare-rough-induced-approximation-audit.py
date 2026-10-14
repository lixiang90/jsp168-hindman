from pathlib import Path
import re

prefix = 'round-rough-induced-approximation'
stems = ['RoughUniformLipschitzApproximation', 'RoughCompactFamilyApproximation',
    'RoughScalarFamilyApproximation', 'RoughNativeOrbitSourceMetric',
    'RoughNativeOrbitApproximation', 'RoughFiniteFamilyApproximation',
    'RoughNativeKernelApproximation', 'RoughNativeFiniteResidueApproximation',
    'RoughFamilyApproximateDiscrepancy', 'RoughFrozenApproximateDiscrepancy']
modules = ['Hindman168/' + s + '.lean' for s in stems]
components = [
    'RoughUniformLipschitzApproximation constructs actual bounded real Lipschitz approximants by infima of distance cones. One K=2B/delta precedes every function with the specified common bound and modulus. Uniform approximation error is at most epsilon and the same supremum bound B is preserved.',
    'RoughCompactFamilyApproximation derives the common modulus from a jointly continuous map on an actual compact product. One approximant Lipschitz constant precedes every left parameter and every original Lip-Lipschitz test bounded by B. No smooth metric or Lipschitz regularity of the map is assumed.',
    'RoughScalarFamilyApproximation restricts the actual left scalar parameter to the compact interval [-R,R], retaining one constant before every scalar and original test.',
    'RoughNativeOrbitSourceMetric defines the metric on the actual conjugate subgroup quotient by pulling back the original specified nilmanifold metric through the proved injective orbit map at left identity. For a compact source it proves equality with the natural quotient topology and compactness in the pulled-back metric. No normality or replacement of the original quotient is assumed.',
    'RoughNativeOrbitApproximation proves joint scalar orbit continuity in these actual metrics by composing the original native scalar action with the isometric orbit inclusion. On any actual compact conjugate subgroup quotient it obtains uniformly bounded Lipschitz approximants for the induced original tests.',
    'RoughFiniteFamilyApproximation combines a finite dependent family of actual compact source spaces with one shared approximant constant, the sum of the individual constants. The constant precedes the residue index, scalar parameter, original observable and approximation function.',
    'RoughNativeKernelApproximation applies the actual rational character-kernel conjugated lattice compactness theorem, discharging source compactness rather than assuming it, and obtains the induced-test approximants on each actual residue kernel quotient.',
    'RoughNativeFiniteResidueApproximation applies the finite family theorem to all actual residue character-kernel quotients, each with its proved compact pulled-back metric. A single constant works for the finite family before its residue index, bounded left scalar and original test are chosen.',
    'RoughFamilyApproximateDiscrepancy proves that a uniformly chosen bounded Lipschitz approximant retains finite probability discrepancy at least eta-2epsilon on every member of the dependent compact family.',
    'RoughFrozenApproximateDiscrepancy accounts for BOTH actual freezing error and approximation error under both original finite probability laws. Retained discrepancy is at least eta-2(epsilon_freeze+epsilon_approx), with estimates needed only on the original supports.',
]
remaining = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'Uniform prescribed-error Lipschitz approximation for induced tests on actual compact conjugate kernel quotients is now proved, including a single constant for all members of a fixed finite residue family and compact left scalar parameters. '
    'The pulled-back source metrics have their actual natural quotient topology and compactness proved; the original metric is retained. '
    'The induced tests themselves have not been claimed Lipschitz in arbitrary compatible metrics. Their bounded approximants preserve discrepancy with an explicit two-law error loss, combined with the proved freezing loss. '
    'Exact original residue sampling weights, mixture disintegration, subbox partition geometry and assembly with convex selection remain open. '
    'The quantitative Leibman obstruction, affine substituted-polynomial coefficient identity, corrected box comparison, stretched-filtration prerequisites, finite density extraction, dimension induction and uniform rough-step comparison remain open. '
    'Package finite native readings and connect conditional face laws. Buffered short-bin geometry, prior-event positive probability, extra-conditioning posterior control, quantitative native smooth-observable bounds, conditional face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
source = Path('round-rough-slow-freezing-audit.py').read_text(encoding='utf-8')
for name, value in {'PREFIX': prefix, 'OLD': 'round-rough-slow-freezing',
        'MODULES': modules, 'COMPONENTS': components, 'REMAINING': remaining}.items():
    source, count = re.subn('^' + name + r'\s*=.*$', lambda _: name + ' = ' + repr(value), source, flags=re.M)
    assert count == 1, name
a = source.index('application_review=COMPONENTS+')
b = source.index('verified=summary', a)
review = [
    'Section 06 passes from frozen original tests to compact smaller character-kernel quotients. The paper specifies a smooth metric, while NativeNilmanifoldData specifies only a compatible metric. The new proof supplies the prescribed-error conclusion needed for induction via Lipschitz approximation, not an unsupported assertion that smooth induced tests are Lipschitz in every compatible metric.',
    'The exact source quotient is L/(conjugate(Gamma,sigma).comap L.subtype). Its metric is pulled back via hDelta -> h*sigma Gamma, whose injectivity and closed embedding were previously proved without normality. Both its natural quotient topology equality and compactness in the metric are established. It is not an abstract surrogate space.',
    'Scalar orbit continuity is established in the original specified target metric and actual pulled-back source metric. It uses the original continuous action exp(tV) on the original quotient, with exp(tV)*h*sigma in exactly that multiplication order.',
    'The infimum cone approximant is bounded below by -B and above by f(x), so its infimum is legitimate and the same absolute bound B holds. The near-distance modulus and far-distance 2B bound give f-epsilon <= g <= f. The common constant depends on B and the fixed positive modulus scale, not on a later test.',
    'For a fixed finite family of residues and fixed original V and rational kernel, the common constant precedes every residue index, bounded scalar left factor, original Lip-Lipschitz bounded test and original finite probability mass. It can depend on fixed native data, the finite residue family, R,B,Lip and epsilon. No uniformity in a later-changing residue family or epsilon tending to zero is claimed.',
    'The actual kernel wrapper retains all rationality hypotheses on S, the character and V, and discharges quotient compactness from the previously proved rational conjugated lattice theorem. Nonempty quotient instances follow from their actual group quotient, not an extra existence assumption.',
    'Both finite probability laws pay their own approximation error. Combined freezing and approximation retain eta-2(epsilon_freeze+epsilon_approx). Applying an approximant without this loss would be invalid and is not done here.',
    'These results supply the regularity supporting step. They do not prove smaller-dimensional uniform equidistribution, native-data packaging of the smaller nilmanifold, the quantitative obstruction, original residue sampling weights or the final StrongConjecture.',
    'All retained source hashes and transitive axiom sets are unchanged. These are author-side checks, not independent kernel replay.',
]
source = source[:a] + 'application_review=COMPONENTS+' + repr(review) + '+[REMAINING],\n        ' + source[b:]
source = re.sub("reference_scope='[^']*'", "reference_scope='06_rough_progressions compact induced tests and finite-residue Lipschitz approximation with explicit discrepancy loss'", source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print('Prepared audit for', len(modules), 'modules.')
