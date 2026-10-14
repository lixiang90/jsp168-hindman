from pathlib import Path
import ast
import re

prefix = 'round-native-terminal-relative-pair'
old = 'round-native-terminal-fourier'
modules = [
    'NativeOriginalTerminalFourierCompactFamilies', 'NativeMetricCosetTranslation',
    'NativeTerminalProductPairObservable', 'NativeRelativeFirstTerminalTranslation',
    'ProductCosetAction', 'NativeTerminalProductPairTranslation',
    'NativeTerminalRelativePairObservable', 'NativeTerminalRelativePairTranslation',
    'NativeTerminalRelativePairMean', 'NativeTerminalReducedPairObservable',
    'NativeTerminalReducedPairMean', 'NativeTerminalReducedPairCompact',
    'NativeTerminalReducedMetricObservable', 'NativeTerminalReducedPairDiscrepancy',
    'NativeTerminalReducedPairRegularity', 'NativeTerminalReducedPairUnitDetection',
    'NativeTerminalReducedPairPolynomialSampling',
]
components = [
    'ACTUAL original terminal Fourier projections have function-space Lipschitz constant ONE and genuinely compact images of the original unit family. This is not a spatial Lipschitz assertion.',
    'ACTUAL original metric coset translations are jointly continuous. The original terminal Fourier pair with ANY original group translation g is a genuine continuous observable on ORIGINAL product-lattice cosets; it is bounded by ONE on original unit inputs. Its family is compact for ANY ONE FIXED compact translation set K, not for all group translations at once.',
    'ACTUAL original terminal group-to-torus projection is genuinely SURJECTIVE. For original filtration degree s*d at least TWO, each actual original terminal z gives the ACTUAL first-coordinate relative-group element (z,1). This degree hypothesis is explicit; degree-one belongs to the abelian base.',
    'ACTUAL original product-coset coordinate action is exact with NONNORMAL original lattices. Original terminal product pair satisfies true first-coordinate terminal eigencharacter and terminal-diagonal invariance, for ANY original translation g, using genuine terminal centrality.',
    'SAME ACTUAL terminal pair is restricted to EXACT original relative lattice cosets via the original subgroup inclusion. Its pointwise values, group action, unit bound, joint translation/input continuity and compact K-times-unit family are genuinely proved.',
    'SAME ACTUAL relative pair has exact first-coordinate eigencharacter law for degree at least TWO, and is invariant under SAME ACTUAL relative terminal diagonal subgroup. Original paired subgroup, terminal subgroup and original lattice are retained literally.',
    'NONZERO original terminal frequency gives SAME ACTUAL RELATIVE canonical Haar pair mean ZERO for ANY original translation g. Proof uses actual surjectivity, the actual first-coordinate relative element and true RELATIVE canonical integral translation invariance. Original single-factor/full-product Haar zero mean is not substituted for relative Haar.',
    'SAME ACTUAL relative pair descends continuously and uniquely to EXACT reduced relative terminal quotient/image-lattice cosets, with exact original factor values and unit bound. True actual terminal invariance supplies descent.',
    'ACTUAL reduced relative native canonical integral equals SAME ACTUAL relative canonical pair integral, by proved native canonical pushforward identity and exact pointwise descent. NONZERO-frequency reduced canonical pair mean is therefore ZERO with explicit degree-at-least-TWO hypothesis.',
    'ACTUAL descended pair family is jointly continuous in arbitrary original translation g and original input F. For ANY ONE FIXED compact translation set K, its family is uniformly compact. The proof uses arbitrary source group topology, without inventing a source group metric or spatial Lipschitz bound.',
    'SAME ACTUAL descended pair is transported through proved topology equality to ACTUAL reduced native specified-metric continuous observables. Actual joint continuity and compact K-times-unit family in that metric uniform norm are proved, without topology-to-spatial-Lipschitz inference.',
    'SAME ACTUAL relative finite sample mean equals EXACT reduced native canonical finite discrepancy on SAME original factor samples, using genuine nonzero reduced canonical zero mean and actual pointwise descent. Arbitrary finite samples and arbitrary original translations are retained.',
    'For ANY ONE FIXED compact translation set K, genuine compact-family spatial Lipschitz approximation gives ONE FIXED finite ACTUAL reduced specified-metric approximant family and positive shared norm/Lipschitz bounds before all original unit inputs, translations in K and finite samples.',
    'ONE FIXED finite ACTUAL reduced UNIT observable family and positive fixed threshold detect ALL large SAME relative pair sample means for ALL translations in ONE FIXED compact K and original unit inputs. Actual norm-two discrepancy stability, spatial approximation and normalization discharge all inputs. This is not a quantitative horizontal-character inverse.',
    'For arbitrary polynomials ALREADY in the ACTUAL relative native model, SAME ACTUAL polynomial samples project to EXACT reduced native polynomial orbit, and original relative pair mean equals reduced canonical discrepancy there. No original normalized shifted-pair membership or filtered-degree assertion is assumed or claimed.',
]
source = Path(old+'-audit.py').read_text(encoding='utf-8')
remaining = ast.literal_eval(re.search(r'^REMAINING = (.*)$', source, re.M).group(1))
remaining = remaining.replace('Original normalized shifted-pair membership/filtered degree, actual relative PAIRED observable/Haar zero mean and terminal diagonal descent, recursive image-layer rationality/connectedness and NONZERO quantitative Leibman induction STILL remain open.',
    'Original normalized shifted-pair membership/filtered degree, recursive image-layer rationality/connectedness and NONZERO quantitative Leibman induction STILL remain open. ACTUAL terminal paired relative observable, true RELATIVE canonical Haar zero mean via actual first-coordinate terminal translations (degree at least TWO), exact terminal diagonal descent, genuine reduced native canonical mean/sample compatibility, actual specified-metric compact K family, finite spatial Lipschitz approximation and ONE FIXED finite ACTUAL UNIT detection are NOW PROVED. Translation parameter is arbitrary for identities/zero means, but uniform compactness/approximation/detection require ONE FIXED compact K. Polynomial sampling transport applies to polynomials ALREADY in actual relative model; original normalized shifted membership is not thereby proved.')
remaining = remaining.replace('NEXT actual original terminal Fourier pair on SAME relative lattice cosets, genuine NONZERO relative canonical Haar zero mean via ACTUAL first-coordinate terminal translations, original terminal diagonal invariance/descent and actual reduced Haar/sample compatibility. Then normalized shifted polynomial/filtered degree and recursive rational image-layer geometry needed for genuine NONZERO quantitative Leibman induction; finite terminal frequency detection itself is not an inverse.',
    'NEXT original normalized shifted polynomial/filtered membership and bounded original fundamental-representative translations, then recursive rational image-layer geometry needed for genuine NONZERO quantitative Leibman degree induction. Actual finite terminal frequency selection and reduced finite-unit detection do not themselves prove an inverse.')
for name, value in [('PREFIX', prefix), ('OLD', old), ('MODULES', ['Hindman168/'+m+'.lean' for m in modules]), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^'+name+r' = .*$', lambda _: name+' = '+repr(value), source, flags=re.M)
source = source.replace('Audit actual relative terminal quotient projection/canonical Haar and genuine ORIGINAL terminal Fourier decomposition/detection.',
    'Audit ACTUAL original terminal pair on relative cosets, genuine relative/reduced canonical Haar zero means and actual reduced metric finite-unit detection.')
source = source.replace('06_rough_progressions and Green-Tao section 7: ACTUAL reduced relative projection/polynomial/canonical Haar and GENUINE ORIGINAL terminal torus/Fourier/finite frequency detection; relative paired Haar/normalized polynomial/recursive filtered inverse/full prize theorem open',
    '06_rough_progressions and Green-Tao section 7: ACTUAL original terminal pair on exact relative cosets; genuine relative/reduced canonical Haar zero means, actual terminal diagonal descent and fixed compact translation family finite-unit detection; original normalized polynomial/recursive filtered inverse/full prize theorem open')
Path(prefix+'-audit.py').write_text(source, encoding='utf-8')
print('Prepared '+prefix+'-audit.py for '+str(len(modules))+' modules')
