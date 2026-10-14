from pathlib import Path
import re

prefix = 'round-rough-packaged-descent'
stems = ['RoughNativeKernelMap', 'RoughNativeKernelSpatialPolynomial',
    'RoughNativeKernelDegreeBound', 'RoughRescaledPieceSelection', 'RoughRescaledPieceLabel',
    'RoughNativeModelFiniteResidue', 'RoughNativePackagedResidueApproximation', 'RoughConjugateResidueTest']
modules = ['Hindman168/' + s + '.lean' for s in stems]
components = [
    'RoughNativeKernelMap constructs the actual exp(-aV)*P*exp(-mV) map with values in the exact packaged kernel nilmanifold. Its actual subgroup native logarithm is represented by a constructed vector multivariate polynomial for all real parameters, with the previously proved degree bound.',
    'RoughNativeKernelSpatialPolynomial substitutes only spatial coordinates by u+Ky in this actual new native logarithm polynomial. The progression parameter is unchanged, every real evaluation is the actual packaged kernel map evaluation, and total degree is preserved.',
    'RoughNativeKernelDegreeBound proves monotonicity of the explicit degree factor and bounds it using the original NativeNilmanifoldData nilpotence step. The resulting uniform degree bound applies to any vector target, including the new smaller native model.',
    'RoughRescaledPieceSelection combines actual frozen/approximated original-law piece selection with exact residue-coordinate uniform-law transport. It constructs a rescaled box and one transformed step-t residue, proves both supports have positive cardinality, and preserves the selected discrepancy threshold without loss.',
    'RoughRescaledPieceLabel proves that every unrestricted transformed sample in the selected box has exactly the original selected geometric label after x=u+Ky. Label-indexed tests therefore specialize to the selected piece test on every new sample.',
    'RoughNativeModelFiniteResidue constructs a member of Fin K for the integer spatial model at each original integer progression index. This member works for all spatial integer points with the prescribed coordinate residues, and its actual exponential coset equals the joint rational model exponential coset.',
    'RoughNativePackagedResidueApproximation identifies the finite-family induced-test approximation with the exact new NativeNilmanifoldData quotient and its specified metric. A single Lipschitz bound is chosen before the residue member, bounded frozen scalar and original observable.',
    'RoughConjugateResidueTest proves the exact ordered quotient test replacement from equality of the right cosets and combines it with freezing error. No lattice normality or reordered factors are assumed.',
]
remaining = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'Actual packaged kernel maps, their all-real joint native logarithmic polynomials after spatial affine substitution, original-step uniform degree control, exact nonempty rescaled piece selection, finite model cosets and induced-test metric interfaces are now proved. '
    'Assemble the native freezing modulus and uniform finite-residue approximants with the selected geometric labels and choose one fixed quotient along unbounded bad progression lengths. '
    'Quantitative Leibman obstruction and its uniform finite character list, affine substituted-coefficient identity, corrected box comparison, stretched filtration, finite density extraction, dimension induction and uniform rough-step comparison remain open. '
    'Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs, and final ordered positive rapidly separated monochromatic extraction remains open. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
review = [
    'The new kernel map is literally the original ordered exponential factorization and is proved to lie in the specified character kernel at every real input. Its quotient lattice may vary with the finite residue index; its actual group and native logarithm remain the packaged structures.',
    'The native vector polynomial represents the genuine new-model logarithm, rather than a projection assumed to be a logarithm. The checked subgroup logarithm identity and constructed linear retraction discharge this obligation.',
    'Spatial substitution fixes the progression parameter and is valid for all real spatial and progression inputs. Neither integer-only interpolation nor polynomiality on sample supports is substituted for joint logarithmic polynomiality.',
    'Both new supports are proved nonempty from the original selected positive-cardinality piece and exact uniform-law pushforward. Their nonemptiness is not inferred from a discrepancy threshold that might be nonpositive.',
    'The uniform family of actual model exponential cosets has only K members, independently of progression length and interpolation coefficient denominators. Integer-coefficient realization at the specific original progression index is used before reducing its value modulo K.',
    'The original native finite-family Lipschitz approximant theorem uses exactly the pullback metric now stored in the new native data. This is a definitional identification of specified metrics, not an assumed uniform comparison between arbitrary metrics.',
    'Right-factor replacement is established through equality of left cosets and an explicit ordered group calculation. The original lattice is not assumed normal, and no commutation of the frozen factor with the kernel map is used.',
    'The new selection, logarithm, model-coset and test lemmas connect previously separate verified obligations. Their remaining analytic inputs and the full quantitative Leibman/density/dimension induction remain explicit; these wrappers do not assert their existence or prove the final target.',
]
source = Path('round-rough-residue-transport-audit.py').read_text(encoding='utf-8')
for name, value in {'PREFIX': prefix, 'OLD': 'round-rough-residue-transport',
        'MODULES': modules, 'COMPONENTS': components, 'REMAINING': remaining}.items():
    source, count = re.subn('^' + name + r'\s*=.*$', lambda _: name + ' = ' + repr(value), source, flags=re.M)
    assert count == 1, name
a = source.index('application_review=COMPONENTS+')
b = source.index('verified=summary', a)
source = source[:a] + 'application_review=COMPONENTS+' + repr(review) + '+[REMAINING],\n        ' + source[b:]
source = re.sub("reference_scope='[^']*'", "reference_scope='06_rough_progressions actual packaged kernel logarithm, finite model residues, induced tests and exact rescaled selection'", source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print('Prepared audit for', len(modules), 'modules.')
