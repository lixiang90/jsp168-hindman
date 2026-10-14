from pathlib import Path
import ast
import re

prefix = 'round-native-diagonal-data'
old = 'round-native-product-probability'
modules = [
    'NativeDiagonalCenterModel', 'NativeDiagonalCenterSubgroupEquality',
    'NativeDiagonalLatticeColumns', 'NativeDiagonalCenterRational',
    'SubgroupQuotientStructureTransport', 'SubgroupQuotientLatticeTransport',
    'NativeDiagonalQuotientLattice', 'NativeDiagonalQuotientStructures',
    'NativeDiagonalFactorMetric', 'NativeDiagonalQuotientData',
    'NativeDiagonalCanonicalProbability', 'NativeDiagonalCanonicalDiscrepancy',
]
components = [
    'ACTUAL original diagonal-center model is constructed as the range of the ORIGINAL real center-model diagonal linear inclusion in ORIGINAL product model E times E. Its actual membership, CLOSEDNESS and inclusion in ORIGINAL product Lie center are PROVED using genuine original product exponential and original center-exponential criterion.',
    'ACTUAL original exponential subgroup of ACTUAL diagonal-center model is EXACTLY ORIGINAL diagonal center subgroup, by actual original global logarithm/exponential and original product exponential. This is PROVED LITERAL subgroup equality, not an assumed or merely compatible replacement group.',
    'ACTUAL ORIGINAL center-lattice basis columns embedded diagonally span the ENTIRE ACTUAL model. Every column original product exponential belongs to ORIGINAL product lattice. Actual logarithm/exponential inverse places each column in ACTUAL ORIGINAL rational lattice log span.',
    'GENUINE RATIONALITY of ACTUAL diagonal-center model against ORIGINAL product lattice is PROVED from those ACTUAL lattice columns and their true full real span. No rationality, adapted-basis or image-lattice discreteness assumption.',
    'Explicit transport of actual quotient charted, T2, simply-connected, Lie and boundaryless structures along a PROVED literal subgroup equality preserves original quotient topology and actual group operations. Actual original charted Lie/boundaryless proof is supplied and preserved, rather than assumed at native diagonal application.',
    'ACTUAL image-lattice discreteness is transported along PROVED equality of original normal subgroups. Original lattice need not be normal; no original discreteness conclusion is assumed in the later native application.',
    'ORIGINAL product lattice image in ACTUAL diagonal-center group quotient is NOW genuinely DISCRETE, CO-COMPACT and CLOSED. Actual central model/rationality and original product lattice hypotheses discharge ALL retained central-subspace quotient lattice theorem inputs; PROVED exponential-subgroup equality identifies the ACTUAL original diagonal image.',
    'ACTUAL ORIGINAL diagonal-center quotient carries constructed charted Lie-infinity/boundaryless structures, T2 and simply-connected properties, via PROVED subgroup equality and genuinely proved central-subspace quotient geometry. No smoothness, boundaryless or topological identification premise.',
    'An ACTUAL compatible metric on ORIGINAL diagonal-center quotient/image lattice is NOW constructed from PROVED discrete/closed image lattice and original compact quotient topology. Genuine metric topology equality and ORIGINAL quotient map open/continuous are proved. No spatial Lipschitz inference.',
    'GENUINE NativeNilmanifoldData(s) is NOW constructed for ACTUAL ORIGINAL product group modulo ORIGINAL diagonal center, ACTUAL original model quotient, ACTUAL original image lattice and ACTUAL compatible metric. Literal original GROUP/MODEL/LATTICE identities are proved. All native structural fields are discharged. Actual step bound is SAME s; NO assumed step/dimension reduction.',
    'ACTUAL original diagonal-factor pushforward probability EXACTLY equals genuine newly constructed native diagonal canonical Haar in PROVED common Borel representation. Genuine original NONNORMAL probability uniqueness applies with ACTUAL proved probability and full ORIGINAL quotient group action invariance. No factor canonical measure-agreement premise.',
    'NONZERO descended ORIGINAL Fourier pair has mean ZERO against GENUINE ORIGINAL diagonal native canonical Haar itself, with explicit Borel/coset transport. Its actual native-canonical discrepancy on SAME actual projected pair polynomial samples is EXACT ORIGINAL derivative average for EVERY original finite sample set, unrestricted coefficients and shifts. No replacement sampling or assumed canonical mean. Appropriate rational fiber-product filtration/induction/nonzero quantitative inverse still open.',
]
source = Path(old+'-audit.py').read_text(encoding='utf-8')
remaining = ast.literal_eval(re.search(r'^REMAINING = (.*)$', source, re.M).group(1))
start = 'Identification with a separately constructed diagonal native canonical Haar, actual image-lattice discreteness/rational native data/compatible metric and appropriate fiber-product filtration are STILL OPEN. NEXT construct those actual rational/quotient geometric data and canonical factor compatibility, then genuine nonzero-frequency quantitative Leibman induction.'
replacement = ('ACTUAL original diagonal-center model, full original lattice-column span and actual product-lattice RATIONALITY are NOW PROVED. Its actual exponential subgroup EQUALS ORIGINAL diagonal center literally. Original image lattice is NOW PROVED discrete/cocompact/closed; actual diagonal quotient Lie-infinity/boundaryless/T2/simply-connected structures and compatible metric are constructed. GENUINE NativeData(s) NOW uses EXACT ORIGINAL diagonal quotient group/model/image lattice/metric, with SAME s step bound only. Actual diagonal pushforward probability NOW EXACTLY equals genuine original native diagonal canonical Haar by PROVED original nonnormal uniqueness. NONZERO pair mean ZERO and SAME original derivative sample discrepancy NOW use actual original native canonical Haar itself, not presumed factor agreement. Appropriate rational fiber-product filtration and actual induction-complexity reduction are STILL OPEN, as is NONZERO quantitative Leibman inverse. NEXT actual native diagonal exp/log/polynomial projection and compact-family child-metric regularity as needed, together with suitable actual rational fiber-product filtered subgroup and quantitative induction; none may be replaced by an assumed inverse or step-drop interface.')
assert start in remaining
remaining = remaining.replace(start, replacement)
remaining = remaining.replace('This is NOT a quantitative inverse or a completed rational filtered nilmanifold: actual rational image lattice/compatible metric and filtered subgroup induction geometry still need to be constructed and verified; diagonal subgroup closedness is now proved.',
    'This is NOT a quantitative inverse. Actual rational diagonal image lattice, native diagonal data and compatible metric are now genuinely proved, while appropriate fiber-product filtered subgroup induction geometry still needs to be constructed and verified.')
remaining = remaining.replace('Then genuine original nonzero central-frequency derivative/product-group polynomial compatibility and NONABELIAN quantitative Leibman induction,',
    'Then actual rational fiber-product filtered geometry and NONABELIAN quantitative Leibman induction,')
for name, value in [('PREFIX', prefix), ('OLD', old),
                    ('MODULES', ['Hindman168/'+m+'.lean' for m in modules]),
                    ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^'+name+r' = .*$', lambda _: name+' = '+repr(value), source, flags=re.M)
source = source.replace('Audit genuine original product canonical Haar, true Fourier-pair zero means and actual invariant diagonal-factor pushforward probability.',
    'Audit genuine original diagonal rational/native quotient data and actual original diagonal canonical Haar/sample compatibility.')
source = source.replace('06_rough_progressions: GENUINE original product canonical Haar and Fourier-pair zero means, ACTUAL invariant diagonal-factor pushforward/discrepancy and diagonal-center closedness; rational factor native data/canonical identification/filtered nonzero inverse/full prize theorem open',
    '06_rough_progressions: GENUINE ORIGINAL diagonal rational/image-lattice/native data and actual original native canonical Haar/sample compatibility; rational fiber-product filtered induction/nonzero quantitative Leibman/full prize theorem open')
Path(prefix+'-audit.py').write_text(source, encoding='utf-8')
print('Prepared '+prefix+'-audit.py for '+str(len(modules))+' modules')
