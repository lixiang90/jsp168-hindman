from pathlib import Path
import ast
import re

prefix = 'round-native-relative-reduction'
old = 'round-native-relative-data'
modules = [
    'SubgroupInclusionTransport', 'NativeRelativeInclusion',
    'NativeRelativeExponentialLogarithm', 'DiagonalLinearModel',
    'NativeDiagonalLayerExponential', 'NativeRelativeTerminalModel',
    'NativeRelativeTerminalCenter', 'NativeRelativeDiagonalInclusion',
    'NativeRelativeTerminalRational', 'NativeRelativeTerminalSubgroup',
    'NativeRelativeReducedLattice', 'NativeRelativeReducedStructures',
    'NativeRelativeReducedMetric', 'NativeRelativeReducedData',
    'NativeRelativeReducedNativeFiltration',
]
components = [
    'ACTUAL original subgroup inclusion smoothness and identity derivative transport along PROVED literal subgroup equality, retaining ORIGINAL chart, topology and group operations. Genuine source smoothness/derivative is supplied, not assumed at the native relative application.',
    'ACTUAL original relative NativeData group inclusion into ORIGINAL product group and actual model continuous linear inclusion are constructed. Actual inclusion is genuinely smooth and its identity derivative is EXACT original model inclusion, by proved original subgroup equality and true native Lie-subalgebra geometry.',
    'GENUINE ACTUAL relative native exponential and global logarithm NOW preserve SAME ORIGINAL product group/model inclusions exactly, via true smooth-hom ODE uniqueness and actual global inverses. No inclusion Exp/Log compatibility premise.',
    'ACTUAL diagonal real subspace of a specified original model layer is constructed, with exact original membership and actual diagonal-vector inclusion. No replacement entire-center model.',
    'ORIGINAL product exponential belongs to ACTUAL specified original diagonal group layer IFF original vector belongs to SAME original diagonal Lie-model layer. Original exponential injectivity and exact original stretched group/Lie layer identity prove the equivalence.',
    'ACTUAL terminal diagonal subspace is NOW constructed INSIDE ACTUAL original relative NativeData model, as the original diagonal-layer inverse image under ACTUAL model inclusion. Genuine closedness and EXACT original relative exponential/internal-terminal membership are proved.',
    'SAME original internal terminal group layer is NOW genuinely CENTRAL in ACTUAL relative NativeData group; actual terminal model is contained in ACTUAL relative Lie center. Its actual central-subspace exponential subgroup EQUALS SAME original internal terminal layer literally. Original relative Exp compatibility and genuine original terminal centrality discharge all inputs.',
    'ACTUAL diagonal continuous linear inclusion from original model into ACTUAL relative native model is constructed for positive stretch. ENTIRE ACTUAL terminal subspace EQUALS image of SAME original terminal Lie layer under this actual inclusion, with exact original product values. No full-span assumption.',
    'ACTUAL diagonal inclusion preserves ORIGINAL rational log-span directions into ACTUAL relative restricted-lattice rational log span, by genuine original positive powers and exact relative exponential inclusion. These directions span ENTIRE actual terminal subspace, so its rationality against SAME original relative restricted lattice is NOW PROVED. No terminal rationality or additive Log Gamma premise.',
    'SAME original internal terminal layer is explicitly typed in ACTUAL relative NativeData group, with LITERAL original subgroup identity, actual normality and exact actual central-subspace subgroup identity. This handles opaque native E/G aliases while preserving SAME original operations.',
    'ORIGINAL relative restricted lattice image in quotient by SAME actual terminal diagonal is NOW genuinely DISCRETE, CO-COMPACT and CLOSED; SAME original terminal subgroup is CLOSED. Actual terminal-center/rationality and retained original native lattice facts discharge ALL central-subspace image-lattice hypotheses. Original restricted lattice need not be normal.',
    'ACTUAL ORIGINAL relative group modulo SAME original internal terminal diagonal NOW carries genuine constructed chart/Lie-infinity/boundaryless/T2/simply-connected structures. Actual central-subspace quotient geometry and PROVED literal original subgroup equality discharge every structure-transport input.',
    'ACTUAL compatible metric on SAME ORIGINAL reduced relative image-lattice coset quotient is NOW constructed from PROVED original image-lattice/closedness facts and actual original topology. True metric topology equality and SAME original open quotient map are proved. No spatial Lipschitz inference.',
    'GENUINE NativeNilmanifoldData(s) is NOW constructed for EXACT SAME ORIGINAL relative group modulo SAME original internal terminal diagonal, ACTUAL model quotient, SAME original restricted-lattice image and ACTUAL compatible metric. LITERAL group/model/lattice identities are proved; ALL structural, terminal/rationality/lattice/metric fields are discharged. SAME step bound s ONLY; no unsupported original nilpotency-step or dimension drop.',
    'ACTUAL PROVED reduced relative filtration is NOW explicitly on SAME ACTUAL reduced NativeData group. Genuine commutator/antitone conditions, initial zero/one top and terminal index s*stretch with every later layer bot are PROVED, retaining the original FILTRATION-degree reduction. This native geometry/filtration does NOT yet prove normalized polynomial membership, terminal-layer Fourier/Haar/sample compatibility or NONZERO quantitative Leibman inverse.',
]
source = Path(old+'-audit.py').read_text(encoding='utf-8')
remaining = ast.literal_eval(re.search(r'^REMAINING = (.*)$',source,re.M).group(1))
start = 'Actual reduced relative quotient by terminal diagonal still needs native model/image-lattice geometry and canonical Haar/sample/normalized shifted polynomial compatibility; terminal-layer Fourier and NONZERO quantitative Leibman remain open.'
replacement = ('ACTUAL relative native inclusion smoothness/identity derivative and SAME original product Exp/Log compatibility are NOW PROVED. ACTUAL terminal diagonal subspace inside ACTUAL relative native model is constructed, closed, in its actual Lie center and genuinely RATIONAL against SAME original relative restricted lattice. Its actual exponential subgroup EQUALS SAME original internal terminal layer literally. ORIGINAL image lattice in quotient by SAME terminal diagonal is NOW PROVED discrete/cocompact/closed; actual quotient chart/Lie-infinity/boundaryless/T2/simply-connected and compatible metric/topology/open quotient are constructed. GENUINE reduced relative NativeData(s) NOW uses EXACT SAME original terminal quotient group/model/image lattice/metric, with literal original identities and SAME step bound s only. ACTUAL reduced relative filtration is NOW on SAME actual native group, with initial zero/one top and terminal index s*stretch. Canonical Haar/sample/normalized shifted polynomial compatibility, terminal-layer Fourier and NONZERO quantitative Leibman degree induction remain open.')
assert start in remaining
remaining = remaining.replace(start,replacement)
remaining = remaining.replace('NEXT actual original relative native inclusion smoothness/identity derivative/Exp-Log compatibility, actual terminal diagonal subspace and rational central quotient native geometry, then terminal-layer Fourier and normalized polynomial/observable/Haar identities needed for genuine NONZERO quantitative Leibman degree induction.',
    'NEXT actual reduced relative native quotient smooth projection/identity derivative/Exp-Log/polynomial compatibility, actual image-layer rational filtered geometry as needed, terminal-layer Fourier and normalized shifted polynomial/observable/canonical-Haar identities needed for genuine NONZERO quantitative Leibman degree induction.')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',['Hindman168/'+m+'.lean' for m in modules]),('COMPONENTS',components),('REMAINING',remaining)]:
    source = re.sub(r'^'+name+r' = .*$',lambda _:name+' = '+repr(value),source,flags=re.M)
source = source.replace('Audit genuine original rational relative-square Lie geometry, restricted lattice and exact original native relative data.', 'Audit actual original relative Exp/Log inclusion, rational terminal diagonal and exact reduced native quotient/filtration.')
source = source.replace('06_rough_progressions and Green-Tao section 7: GENUINE ORIGINAL rational relative Lie model, actual restricted lattice and EXACT ORIGINAL relative NativeData(s); reduced terminal quotient geometry/Haar/normalized polynomial/nonzero quantitative Leibman/full prize theorem open', '06_rough_progressions and Green-Tao section 7: ACTUAL relative Exp/Log inclusion, genuine rational terminal diagonal and EXACT reduced native quotient/image lattice/metric/filtration; terminal Fourier/Haar/normalized polynomial/nonzero quantitative Leibman/full prize theorem open')
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
print('Prepared '+prefix+'-audit.py for '+str(len(modules))+' modules')
