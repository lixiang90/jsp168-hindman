from pathlib import Path
import re

prefix = 'round-rough-geometric-descent'
stems = ['RoughBalancedCuts', 'RoughIntervalPartition', 'RoughBoxPartition',
    'RoughBalancedBoxGeometry', 'RoughPartitionWeightComparison',
    'RoughPartitionPieceSelection', 'RoughPartitionScaleThresholds',
    'RoughFrozenPartitionSelection', 'RoughNativeSubgroupNilmanifold',
    'RoughNativeKernelNilmanifold']
modules = ['Hindman168/' + s + '.lean' for s in stems]
components = [
    'RoughBalancedCuts constructs actual balanced integer cuts by distributing the quotient and remainder of each original side length. Every consecutive length is between floor(length/N) and floor(length/N)+1. The endpoints and monotonicity are proved. For length at least 2N each side lies between length/(2N) and 2length/N, including the final piece.',
    'RoughIntervalPartition proves coverage and uniqueness for finite interval cuts, constructs an actual finite interval label, and proves its original step-class fibers equal the exact cut subintervals. The label is defined for every integer; fiber specifications are restricted to the original interval.',
    'RoughBoxPartition constructs finite labels consisting of the interval index vector and the actual K-residue vector. For every signed endpoint and original residue, its original step-t sample fibers are exactly the subbox step-t/K intersections and its unrestricted fibers are exactly the subbox K classes.',
    'RoughBalancedBoxGeometry proves containment, the paper-form subbox upper and lower side bounds, pointwise coordinate oscillation bounds inside each piece, and nonempty coprime residue intersections under the actual original side threshold 2NtK.',
    'RoughPartitionWeightComparison applies the previously proved original count comparison to the actual geometric label fibers. There are exactly N^dimension*K^dimension labels. Total absolute weight difference is at most this fixed number times dimension times 5t/(cZ), uniformly in endpoints, original residues and piece choices.',
    'RoughPartitionPieceSelection combines actual uniform fiber expectation disintegration with the geometric weight comparison. A positive-cardinality original subbox/residue intersection retains any discrepancy threshold below the original discrepancy minus M times the total weight bound. The discrepancy is not divided by the number of pieces.',
    'RoughPartitionScaleThresholds derives one eventual threshold from PowerDominates before every varying natural t with t<=2S. It gives positive Z, original side size at least 2N, piece nonempty threshold 2NtK, original denominator threshold 2t, and any prescribed supremum-weight loss. N,K,dimension,c,M and error tolerance remain fixed before varying data.',
    'RoughFrozenPartitionSelection assembles original two-probability freezing and approximation errors with geometric piece selection. The retained discrepancy exceeds theta provided theta plus the actual weight majorant plus 2*(freeze_error+approximation_error) is below the original discrepancy. Both original parent laws are proved nonempty; errors need only hold on the original box.',
    'RoughNativeSubgroupNilmanifold packages the actual connected simply connected rational Lie subgroup and its actual conjugate lattice intersection as NativeNilmanifoldData at the original nilpotence step. It retains the original subgroup topology, proved compact quotient, discrete intersection, genuine subgroup Lie structure, and the original orbit-pullback metric with its proved open quotient map.',
    'RoughNativeKernelNilmanifold specializes this construction to the actual rational horizontal character kernel for every integer coset index. The resulting group and lattice are proved to be the original kernel and conjugate intersection. A nonzero restricted character gives strict model finrank decrease relative to the original native nilmanifold.',
]
remaining = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'The actual bounded geometric subbox/residue partition, uniform side thresholds, original finite-piece weight comparison, freezing/approximation loss assembly, and smaller native character-kernel nilmanifold packaging with strict dimension decrease are now proved. '
    'Apply native freezing and the uniform finite-residue induced-test approximants to the constructed piece labels; connect their maps and polynomial coordinates to the packaged kernel data. '
    'Prove the actual x=u+Ky conditional sampling transport and comparable transformed-box bounds, preserving uniform constants and logarithmic joint polynomiality in the new native model. '
    'The quantitative Leibman obstruction, affine substituted-polynomial coefficient identity, corrected box comparison, stretched-filtration prerequisites, finite density extraction, dimension induction and uniform rough-step comparison remain open. '
    'Package finite native readings and connect conditional face laws. Buffered short-bin geometry, prior-event positive probability, extra-conditioning posterior control, quantitative native smooth-observable bounds, conditional face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
review = [
    'The partition uses fixed N balanced cuts with no clipped final remainder. Exact original signed integer interval endpoints and actual label fibers are proved; a list of numerical piece weights is no longer treated as an assumed geometric partition.',
    'The lower and upper side bounds have precisely the paper form with lambda=1/N. Coordinate diameter at most 2CZ/N suffices for the existing scalar-action freezing modulus after choosing N sufficiently large. Choosing N before varying endpoints is essential; the present geometry theorem does not itself select N from the native modulus.',
    'The actual finite label set has N^d*K^d elements, including potential empty pieces outside the large-scale regime. Original uniform mixture and selection handle zero weights, and the separate 2NtK threshold ensures every intended coprime conditional piece is nonempty.',
    'At the original growth threshold, original side cZ exceeds 2N, 2NtK and 2t uniformly for ALL t<=2S. The total supremum-weight error is below any fixed epsilon. This gives uniform endpoint and residue control, not merely convergence for one fixed box.',
    'The selection wrapper requires the actual original discrepancy and bounded comparison test. The frozen wrapper additionally requires support-wise errors for actual frozen and approximate tests. It proves all losses, but does not silently supply native test maps as hypotheses already discharged.',
    'The kernel data constructor proves every native nilmanifold structural field using the genuine subgroup chart, original conjugated lattice intersection, proved rational compactness and original orbit-pullback metric. No new lattice, normality assumption or smooth compatible metric is introduced.',
    'Strict dimension decrease uses a character nonzero on the specified original Lie subalgebra, whose finrank is at most the original model finrank. The data constructor accepts an arbitrary rational original Lie subalgebra; the ambient top rationality and concrete quantitative-Leibman character choice must still be connected in the full application.',
    'The source-model rational scalar action is constructed by restriction of the real scalar action. Native joint kernel logarithmic polynomiality was previously proved in original ambient coordinates; transfer to the newly packaged subgroup native logarithm remains an explicit obligation.',
    'A decidable predicate mismatch between generic finite labels and concrete product/function labels was repaired using extensional equality of the actual finite filters. No heartbeat limit increase or logical axiom was used.',
    'All retained proof sources and transitive axiom sets are checked against the previous checkpoint. Author-side checks are not independent kernel replay; unproved existence inputs and the final target remain unchanged.',
]
source = Path('round-rough-sampling-weights-audit.py').read_text(encoding='utf-8')
for name, value in {'PREFIX': prefix, 'OLD': 'round-rough-sampling-weights',
        'MODULES': modules, 'COMPONENTS': components, 'REMAINING': remaining}.items():
    source, count = re.subn('^' + name + r'\s*=.*$', lambda _: name + ' = ' + repr(value), source, flags=re.M)
    assert count == 1, name
a = source.index('application_review=COMPONENTS+')
b = source.index('verified=summary', a)
source = source[:a] + 'application_review=COMPONENTS+' + repr(review) + '+[REMAINING],\n        ' + source[b:]
source = re.sub("reference_scope='[^']*'", "reference_scope='06_rough_progressions actual bounded geometric sampling partition and rational character-kernel dimension descent data'", source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print('Prepared audit for', len(modules), 'modules.')
