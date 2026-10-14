from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-full-concatenation-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-full-concatenation-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-full-concatenation'", "PREFIX = 'round-finite-bessel'")
source = source.replace("OLD = 'round-nested-correlation'", "OLD = 'round-full-concatenation'")
modules = ['Hindman168/FiniteProjectionBessel.lean',
           'Hindman168/MixedDualSignedExactModel.lean',
           'Hindman168/MixedDualFiniteBesselEnergy.lean',
           'Hindman168/SubgroupCubeL2Energy.lean',
           'Hindman168/MixedCubeProjectionLimit.lean',
           'Hindman168/MixedDualGowersProjectionEnergy.lean',
           'Hindman168/MixedDualFiniteGowersBessel.lean']
components = [
    'For a fixed finite family of genuine factor projections of the same completed-space vector, pairwise orthogonality bounds their total squared norms by the input squared norm. The subspaces themselves need not be mutually orthogonal. Full subgroup concatenation discharges this hypothesis from orthogonality to the positive-degree off-diagonal sum factors, allowing different degrees. Unit actual inputs have total projection energy at most one when those off-diagonal sum Gowers values vanish. Affine normalization gives an exact signed unit-bounded actual representative of each factor projection. Every actual vertex dual is in the original mixed-dual hull by reflecting its finite vertex labels. A single-vertex replacement by an input with the same factor projection has null weighted cube difference; finite induction replaces all vertices. A positive-order actual unit subgroup cube is bounded by the original weighted Haar L2 energy via the verified averaged-face-square identity. Consequently the limiting degree-d Gowers value a satisfies a^(2^d) <= squared norm of the genuine projection. For every fixed finite family with vanishing off-diagonal concatenated norms, the limiting Gowers powers sum to at most one, and the actual family-mean limit has dyadic power at most 1/M. The exponent is the original paper exponent, not an enlarged substitute. All original cell weights and varying finite groups are retained.'
]
gap = ' The full qualitative Bessel theorem, remaining replica integration, cyclic-to-interval transfer and inverse correlator existence remain missing.'
assert gap in previous.REMAINING
remaining = previous.REMAINING.replace(gap, ' ' + components[0] +
    ' The fixed finite-family ultrafilter Bessel bound still needs uniform finite thresholds and the sampling/selection passage to arbitrarily large, arbitrarily weighted index families. The full qualitative Bessel modulus, remaining replica integration, cyclic-to-interval transfer and inverse correlator existence remain missing.')
for field, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + field + r' = .*$', field + ' = ' + repr(value), source, flags=re.M)
counts = {'1128': '1131', '1113': '1120', '5255': '5271', '1131': '1138', '1122': '1129'}
source = re.sub(r'\b(?:1128|1113|5255|1131|1122)\b', lambda m: counts[m.group()], source)
source = source.replace('== 7', '== 16').replace("'theorem_count': 7", "'theorem_count': 16")
for a, b in [('new_theorems=7', 'new_theorems=16'),
             ('new_axiom_reports=7', 'new_axiom_reports=16'),
             ('new_module_count=3', 'new_module_count=7'),
             ('new_theorem_count=7', 'new_theorem_count=16'),
             ('new_selected_report_count=7', 'new_selected_report_count=16')]:
    source = source.replace(a, b)
review = [
    'PROGRESS. The full-concatenation round was rechecked before edits. The saved baseline retains all original proof-source hashes, the exact previous kernel registry, dependencies and manuscript version. This increment changes only root imports and the selected kernel registry among those retained files.',
    'The generic Bessel argument uses a finite sum of the actual projections of one vector. Its squared norm is the sum of individual squared norms because off-diagonal inner products vanish. Projection correlation equals its squared norm by the genuine projection residual orthogonality. Nonnegativity of the squared residual after subtracting that finite sum proves the total energy bound. Mutual orthogonality of the full subspaces is not assumed.',
    'For the varying subgroup systems, the audited concatenation and full projection preservation make projections of a vector orthogonal when the vector is orthogonal to each off-diagonal sum factor. The finite energy result applies with independently varying positive degrees. Actual unit families have norm at most one in the original weighted Haar realization, giving total energy at most one from vanishing off-diagonal concatenated Gowers values. There is no diagonal vanishing premise.',
    'The signed exact model uses (f+1)/2, an exact unit-interval projection representative t, and q=2t-1. Constant one lies in the original dual factor. Linearity therefore identifies q with the actual projection of f, and its pointwise range is [-1,1]. The model is valid for every positive degree and tail-containing ultrafilter; it is not a separate unproved input assumption.',
    'The finite face-product square bound discards only nonroot unit factors. The genuine positive-order cube is an average of squared subgroup Haar means of faces. Haar square contraction, ambient translation invariance and the face root-square bound prove cube <= ambient L2 energy. Integration multiplies by the original nonnegative cell weights directly. The finite energy inequality itself needs no normalization or replacement of the cell law.',
    'Reflecting vertex labels by symmetric difference with the distinguished vertex gives an explicit bijection of erased finite vertex sets. This realizes an arbitrary vertex dual as a genuine root mixed dual and proves actual hull membership from off-vertex unit bounds. No characteristic-factor membership of these inputs is assumed.',
    'For one vertex replacement, the difference of the actual weighted cube means is the weighted correlation of the actual residual with a unit actual vertex dual. The two vertex duals agree off the replaced vertex. Hull membership puts their common Hilbert representative in the original factor; residual orthogonality annihilates its limiting correlation. Finite-set induction replaces all vertices by mixing the two actual input arrays. Every replacement preserves unit bounds and uses exactly the displayed residual orthogonality.',
    'Applying simultaneous replacement to a unit family and its signed exact projection model transfers the actual cube limit to the model. The finite cube-to-L2 estimate and weighted inner-product convergence then give a^(2^d) <= projection norm squared. This strengthens the earlier projection norm bound to the exact energy exponent required by the paper.',
    'For a fixed finite family, each direction supplies its genuine nonnegative limiting Gowers value and the projection energy bound. Summation and finite Bessel energy give total dyadic powers <=1, including the varying-degree form. The already audited finite Haar dyadic-power inequality gives mean(a)^(2^d) <=1/M. Finite-sum convergence supplies the same bound for the actual stagewise family-mean limit.',
    'A development elaboration timeout at an actual hull-membership goal was repaired by explicitly exposing the genuine vertex-dual function with change. A norm type mismatch was repaired by writing the explicit completed-space image in the limit statement. Failed focused/build commands and warnings are not success evidence. No set_option or increased heartbeat bound is used. Only terminal successful focused compilations, the final full build and the complete selected kernel output count as validation.',
    'Sixteen theorems in seven modules are audited. These follow the fixed-family projection and energy step of Section 8 in the finite-subgroup weighted Haar specialization. Uniform finite thresholds and the sampling passage to arbitrary index families are still missing; this is not a claim that the full qualitative Bessel theorem is complete. Inverse correlator existence, the remaining original-problem integrations and StrongConjecture remain unproved.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://arxiv.org/html/1603.07815v4', reference_scope='Section 8 fixed finite-family projection energy and dyadic Gowers bound; weighted finite-subgroup specialization')\n"
) + source[end:]
Path('round-finite-bessel-audit.py').write_text(source, encoding='utf-8')
print('Prepared seven-module audit: sixteen theorems.')
