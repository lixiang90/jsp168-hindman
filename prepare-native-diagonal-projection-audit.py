from pathlib import Path
import ast
import re

prefix = 'round-native-diagonal-projection'
old = 'round-native-diagonal-data'
modules = [
    'SubgroupQuotientProjectionTransport', 'NativeDiagonalProjectionSmooth',
    'NativeDiagonalQuotientProjection', 'ContinuousMapTopologyTransport',
    'NativeDiagonalPolynomialProjection', 'NativeDiagonalPairMetricObservable',
    'NativeDiagonalPairRegularFamily', 'NativeDiagonalPairMetricDiscrepancy',
    'NativeDiagonalPairUnitDetection',
]
components = [
    'PROVED literal subgroup equality transports ACTUAL smooth quotient projection and its identity derivative into the ACTUAL transported quotient chart. No smoothness or derivative compatibility is assumed at the native application.',
    'ORIGINAL product-to-diagonal quotient projection is genuinely smooth, and its derivative at the identity is EXACT actual real model quotient projection, by retained central-subspace geometry and PROVED subgroup equality.',
    'ACTUAL native diagonal group homomorphism and ACTUAL model continuous linear projection NOW preserve original native product exponential and logarithm exactly. Smooth-hom exponential compatibility uses genuine ODE uniqueness, with all actual projection smoothness and derivative inputs discharged.',
    'Continuous functions transport along PROVED topology equality with SAME point values, continuous function-space transport and, for compact spaces, exact uniform-norm isometry. No spatial Lipschitz inference from topology equality.',
    'ACTUAL projected original product multivariate logarithmic polynomial preserves degree, evaluations, original quotient orbit and logarithm. COMPLETE scalar polynomial and all coefficients under a pulled-back functional are preserved; original coefficients and shifts remain unrestricted.',
    'SAME ORIGINAL descended Fourier-pair observable NOW belongs to continuous functions for ACTUAL diagonal native specified metric, with exact point values, actual function-space continuity and uniform-norm compact original unit-input family.',
    'GENUINE compact-family Stone-Weierstrass Lipschitz approximation supplies ONE FIXED finite ACTUAL diagonal-metric approximant list and shared positive norm/spatial-Lipschitz bounds for ALL original unit inputs before polynomials, shifts and finite samples.',
    'For NONZERO original frequency, ACTUAL diagonal specified-metric observable canonical Haar discrepancy on ACTUAL native projected shifted-pair polynomial orbit is EXACT SAME ORIGINAL derivative finite average, for EVERY finite sample set. Genuine canonical mean zero and original projection/sample identities discharge the equality.',
    'ONE FIXED finite ACTUAL UNIT diagonal-metric observable family and positive threshold detect EVERY large original nonzero-frequency derivative average, before original polynomial coefficients, shifts and finite samples. Norm-two discrepancy stability and genuine complex-linear normalization are proved and applied. This is regularity and detection, NOT a nonzero quantitative inverse or an induction-complexity reduction.',
]
source = Path(old+'-audit.py').read_text(encoding='utf-8')
remaining = ast.literal_eval(re.search(r'^REMAINING = (.*)$', source, re.M).group(1))
start = 'NEXT actual native diagonal exp/log/polynomial projection and compact-family child-metric regularity as needed, together with suitable actual rational fiber-product filtered subgroup and quantitative induction; none may be replaced by an assumed inverse or step-drop interface.'
replacement = ('ACTUAL native diagonal smooth projection, identity derivative, original exp/log compatibility, projected polynomial degree/evaluation/orbit/log and COMPLETE scalar polynomial/coefficient identities are NOW PROVED. SAME descended Fourier pair is NOW transported to ACTUAL specified metric with genuine compactness. ONE FIXED finite genuine spatial Lipschitz approximant family and ONE FIXED finite ACTUAL UNIT family with positive threshold detect ALL large original nonzero-frequency derivative averages on SAME actual projected polynomial orbit and genuine canonical Haar, before all coefficients/shifts/samples. No assumed descended spatial regularity or canonical discrepancy compatibility remains in this step. NEXT suitable actual rational fiber-product filtered subgroup, filtration/degree/complexity induction and NONZERO quantitative Leibman; none may be replaced by an assumed inverse or step-drop interface.')
assert start in remaining
remaining = remaining.replace(start, replacement)
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',['Hindman168/'+m+'.lean' for m in modules]),('COMPONENTS',components),('REMAINING',remaining)]:
    source = re.sub(r'^'+name+r' = .*$', lambda _: name+' = '+repr(value), source, flags=re.M)
source = source.replace('Audit genuine original diagonal rational/native quotient data and actual original diagonal canonical Haar/sample compatibility.', 'Audit actual native diagonal exp/log/polynomial projection and genuine specified-metric finite unit derivative detection.')
source = source.replace('06_rough_progressions: GENUINE ORIGINAL diagonal rational/image-lattice/native data and actual original native canonical Haar/sample compatibility; rational fiber-product filtered induction/nonzero quantitative Leibman/full prize theorem open', '06_rough_progressions: ACTUAL diagonal native exp/log/polynomial projection, specified-metric compact Lipschitz family and finite UNIT original derivative detection; rational fiber-product filtered induction/nonzero quantitative Leibman/full prize theorem open')
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
print('Prepared '+prefix+'-audit.py for '+str(len(modules))+' modules')
