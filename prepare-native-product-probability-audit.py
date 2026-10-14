from pathlib import Path
import ast
import re

prefix = 'round-native-product-probability'
old = 'round-native-fourier-pair'
modules = [
    'NativeBorelProbabilityTranslation', 'ProductCosetProbability',
    'NativeProductCanonicalProbability', 'NativeProductCanonicalIntegral',
    'NativeFourierPairIntegral', 'CentralSubgroupFactorProbability',
    'NativeDiagonalFactorProbability', 'NativeFourierPairFactorIntegral',
    'DiagonalCenterClosed',
]
components = [
    'The ACTUAL original canonical probability in its PROVED Borel representation retains ORIGINAL group translation invariance by explicit sigma-algebra transport and true original invariance. Original raw continuous observables are genuinely integrable against it.',
    'ACTUAL product of invariant probabilities on original NONNORMAL cosets is transported through the ORIGINAL product coset homeomorphism. Actual product group action compatibility, probability, inverse coordinate pushforward and ALL original product-group translation invariance are PROVED. No original lattice normality or product canonical agreement premise.',
    'ACTUAL product of ORIGINAL native probabilities supplies ALL generic Borel/second-countable/probability/invariance hypotheses. Genuine ORIGINAL NONNORMAL probability uniqueness identifies this ACTUAL product-coset probability EXACTLY with actual native product canonical Haar in its proved Borel representation, for every fixed native pair of common step.',
    'Genuine ORIGINAL canonical product integrals equal actual product-coordinate integrals for ALL original complex functions, using explicit actual Borel/coset sigma transport and true measurable homeomorphism. Actual original product canonical probability pushes forward under TRUE original coset coordinates to product of actual original probabilities.',
    'ACTUAL same-frequency paired Fourier observable has ORIGINAL product canonical Haar mean EXACTLY parent Fourier mean times its complex conjugate. True actual product measure and complex product integral theorem prove this. Every NONZERO frequency has genuine ORIGINAL product canonical mean ZERO; no mean-zero premise.',
    'ACTUAL central-subgroup factor pushforward preserves probability, full quotient-group translation invariance and continuous integrals. Actual map equivariance, actual measurable open quotient map and actual original invariant probability discharge each step; original lattice remains nonnormal.',
    'ACTUAL ORIGINAL product canonical Haar pushes forward to genuine invariant probability on ACTUAL original diagonal-center quotient/image lattice. ALL generic probability, Borel, measurability and quotient-group action hypotheses are discharged. This is genuine invariant pushforward, not yet identification with separately constructed factor native canonical Haar; rational image lattice/native geometry remain open.',
    'ACTUAL descended same-frequency pair integral equals ORIGINAL product canonical pair integral. NONZERO frequency thus has actual diagonal-factor pushforward mean ZERO. Its actual finite projected pair orbit discrepancy is EXACT original derivative average on SAME original finite sample set, unrestricted original coefficients and integer shifts. No assumed derivative mean or replacement sampling measure.',
    'The ACTUAL diagonal center subgroup is PROVED CLOSED in ORIGINAL product topology by actual equal-coordinate and commutation equations. This is genuine geometric progress, not yet proof of image-lattice discreteness/rational filtration or native diagonal data. No nilpotency step or original dimension drop is claimed.',
]
source = Path(old+'-audit.py').read_text(encoding='utf-8')
remaining = ast.literal_eval(re.search(r'^REMAINING = (.*)$', source, re.M).group(1))
start = 'NEXT actual product/factor canonical Haar compatibility, actual diagonal quotient native/rational geometry and suitable fiber-product filtration, then genuine nonzero-frequency quantitative Leibman induction.'
replacement = ('Actual original product canonical Haar is NOW genuinely the transported product of ORIGINAL native probabilities, by true original nonnormal uniqueness and actual product group invariance. Exact original canonical product integrals and coordinate pushforward are proved. Actual same-frequency pair mean equals parent Fourier mean times its conjugate, hence NONZERO original pair mean ZERO. ACTUAL diagonal-factor pushforward probability is PROVED probability and fully invariant under its actual quotient-group action; actual descended pair mean is ZERO for nonzero frequencies and actual factor discrepancy equals SAME original finite derivative average. ACTUAL diagonal center is NOW PROVED CLOSED. Identification with a separately constructed diagonal native canonical Haar, actual image-lattice discreteness/rational native data/compatible metric and appropriate fiber-product filtration are STILL OPEN. NEXT construct those actual rational/quotient geometric data and canonical factor compatibility, then genuine nonzero-frequency quantitative Leibman induction.')
assert start in remaining
remaining = remaining.replace(start, replacement)
remaining = remaining.replace('diagonal subgroup closedness/rational image lattice/compatible metric and actual filtered subgroup induction geometry still need to be constructed and verified.',
    'actual rational image lattice/compatible metric and filtered subgroup induction geometry still need to be constructed and verified; diagonal subgroup closedness is now proved.')
for name, value in [('PREFIX', prefix), ('OLD', old),
                    ('MODULES', ['Hindman168/'+m+'.lean' for m in modules]),
                    ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^'+name+r' = .*$', lambda _: name+' = '+repr(value), source, flags=re.M)
source = source.replace('Audit actual same-frequency pair derivative, diagonal-center descent, compact family and exact original shifted polynomial samples.',
    'Audit genuine original product canonical Haar, true Fourier-pair zero means and actual invariant diagonal-factor pushforward probability.')
source = source.replace('06_rough_progressions: ACTUAL Fourier pair derivative and diagonal-center descent, compact bounded family and exact original shifted pair polynomial samples; rational filtered geometry/canonical pair-factor Haar/nonzero-frequency quantitative Leibman/full prize theorem open',
    '06_rough_progressions: GENUINE original product canonical Haar and Fourier-pair zero means, ACTUAL invariant diagonal-factor pushforward/discrepancy and diagonal-center closedness; rational factor native data/canonical identification/filtered nonzero inverse/full prize theorem open')
Path(prefix+'-audit.py').write_text(source, encoding='utf-8')
print('Prepared '+prefix+'-audit.py for '+str(len(modules))+' modules')
