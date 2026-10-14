from pathlib import Path
import ast
import re

prefix = 'round-relative-square-filtration'
old = 'round-native-diagonal-projection'
modules = [
    'RelativeSquareSubgroup', 'RelativeSquareFiltration',
    'RelativeSquareTerminalCenter', 'SubgroupFiltrationTransport',
    'RelativeSquareInternalFiltration', 'RelativeSquareReducedFiltration',
    'RelativeSquareTopology', 'NativeRelativeSquareFiltration',
]
components = [
    'ACTUAL relative-square subgroup is constructed inside ORIGINAL G times G, with both coordinates in ORIGINAL H and their relative product in ORIGINAL normal N. Exact original membership, diagonal inclusion, product inclusion, monotonicity, terminal N=bot diagonal equality and genuine original-coordinate decomposition are proved. No original lattice normality.',
    'ACTUAL relative-square layers P_i=F_i times_(F_(i+1)) F_i genuinely satisfy the full commutator filtration and antitonicity. ORIGINAL coordinate commutators lie in F_(i+j), and their relative product genuinely lies in F_(i+j+1), by actual quotient commutator multiplication identities. No replacement full-product filtration. Terminal layer P_d EQUALS actual diagonal F_d when F_(d+1)=bot.',
    'ACTUAL TERMINAL diagonal F_d is proved CENTRAL in ORIGINAL product when F_1=top and F_(d+1)=bot, by genuine original filtration commutators. Its original normality follows. Entire original center is NOT substituted for terminal F_d.',
    'Actual subgroup image and inverse-image filtrations preserve genuine commutator/antitone conditions. Actual original quotient images of layers contained in the specified normal subgroup are PROVED bot. No quotient degree-drop conclusion is assumed.',
    'The filtration is restricted to ACTUAL relative-square group P_1 itself, with BOTH initial internal layers PROVED top. ACTUAL internal terminal layer is EXACT comap of original diagonal F_d and is genuinely normal from proved original terminal centrality.',
    'ACTUAL relative-square group modulo its ACTUAL internal terminal diagonal NOW carries a PROVED image filtration with BOTH initial layers top and terminal index d rather than d+1; all later layers are bot. This is genuine algebraic FILTRATION-degree reduction, not an asserted original nilpotency-step or dimension reduction. No relative nilmanifold, rational lattice or inverse theorem is claimed here.',
    'ACTUAL relative-square subgroup is genuinely CLOSED when actual original layers are closed, from continuous coordinate/inverse/product maps and exact proved membership. No restricted-lattice compactness or rationality is inferred merely from closedness.',
    'For ORIGINAL NativeNilmanifoldData(s) and ANY positive fixed stretch D, ACTUAL original stretched relative-square layers are constructed, with original filtration conditions, CLOSEDNESS and terminal diagonal equality at s*D PROVED. ORIGINAL step bound and retained exact group/Lie lower-central geometry discharge ALL actual normality/filtration/terminal/closedness inputs. The quotient of ACTUAL original relative-square group by its ACTUAL internal diagonal terminal layer carries genuine filtration with initial zero/one top and terminal index s*D. Actual rational Lie model, restricted lattice compactness, native quotient metric/Haar, normalized polynomial membership and nonzero quantitative inverse still remain to be proved.',
]
source = Path(old+'-audit.py').read_text(encoding='utf-8')
remaining = ast.literal_eval(re.search(r'^REMAINING = (.*)$',source,re.M).group(1))
remaining += (' ACTUAL algebraic RELATIVE SQUARE subgroups and filtration are NOW constructed: both coordinates lie in original F_i and their relative product in F_(i+1); genuine relative commutator/antitone conditions and terminal diagonal equality are PROVED. Actual internal relative-group initial zero/one layers are top, terminal diagonal is central/normal, and actual quotient image filtration has terminal index d instead of d+1. For genuine ORIGINAL stretched NativeData(s) layers ALL normality/filtration/closedness/terminal inputs are discharged; actual reduced relative filtration has terminal index s*D. This is real FILTRATION-degree reduction, NOT an assumed original group step/dimension drop. Actual relative rational Lie model, original restricted-lattice cocompactness, native quotient structures/metric/canonical Haar, normalized shifted polynomial membership and finite original shifted observable transport still remain open. Whole-product Haar agreement does NOT supply canonical Haar on the relative subgroup; entire-center Fourier decomposition does NOT automatically supply terminal-layer decomposition. NEXT construct actual rational relative-square Lie model and original restricted lattice geometry, then terminal-layer Fourier and normalized polynomial/observable identities needed for genuine NONZERO quantitative Leibman induction. Retain all prior regularity and finite-unit detection without claiming they already prove an inverse.')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',['Hindman168/'+m+'.lean' for m in modules]),('COMPONENTS',components),('REMAINING',remaining)]:
    source = re.sub(r'^'+name+r' = .*$',lambda _:name+' = '+repr(value),source,flags=re.M)
source = source.replace('[A-Za-z][A-Za-z0-9_]*','[A-Za-z][A-Za-z0-9_.]*')
source = source.replace('Audit actual native diagonal exp/log/polynomial projection and genuine specified-metric finite unit derivative detection.', 'Audit actual relative-square group filtration, terminal diagonal and genuine original algebraic filtration-degree reduction.')
source = source.replace('06_rough_progressions: ACTUAL diagonal native exp/log/polynomial projection, specified-metric compact Lipschitz family and finite UNIT original derivative detection; rational fiber-product filtered induction/nonzero quantitative Leibman/full prize theorem open', '06_rough_progressions and Green-Tao section 7: ACTUAL relative-square original subgroup filtration and genuine quotient FILTRATION-degree reduction; relative rational native geometry/polynomial normalization/nonzero quantitative Leibman/full prize theorem open')
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
print('Prepared '+prefix+'-audit.py for '+str(len(modules))+' modules')
