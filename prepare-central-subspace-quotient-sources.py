from pathlib import Path
import re

stages = ['SmoothProjection', 'SmoothLift', 'LieGroup', 'Differential', 'Tangent',
          'NativeExponential', 'NativeLogarithm']
for stage in stages:
    src = Path('Hindman168/NativeCenterQuotient'+stage+'.lean').read_text(encoding='utf-8')
    for name, replacement in [('Projection','finiteRealQuotientProjection V'),
                               ('Section_right','finiteRealQuotientSection_right V'),
                               ('Section','finiteRealQuotientSection V')]:
        src = src.replace('nativeCenterQuotient'+name+' (I := I) (G := G)',replacement)
    src = src.replace('nativeLieCenterModel (I := I) (G := G)','V')
    src = src.replace('Subgroup.center G','(nativeCentralSubspaceSubgroup (I := I) V hV)')
    src = src.replace('NativeCenterQuotient','NativeCentralSubspaceQuotient')
    src = src.replace('nativeCenterQuotient','nativeCentralSubspaceQuotient')
    for old in ['NormedModel','Separation']:
        src = src.replace('import Hindman168.NativeCentralSubspaceQuotient'+old,
                          'import Hindman168.NativeCentralSubspaceQuotientCharted')
    src = re.sub(r'(nativeCentralSubspaceQuotient[A-Za-z0-9_]*) (?:\(E := E\) )?\(I := I\) \(G := G\)',
                 r'\1 (I := I) V hV',src)
    marker='attribute [local instance] lieGroup_smooth_min_three'
    src=src.replace(marker,
        'variable (V : Submodule ℝ E) [IsClosed (V : Set E)]\n'
        '  (hV : V ≤ nativeLieCenterModel (I := I) (G := G))\n\n'+marker+'\n'
        'attribute [local instance] nativeCentralSubspaceSubgroup_normal')
    src=src.replace('original center quotient','original specified central-subspace quotient')
    Path('Hindman168/NativeCentralSubspaceQuotient'+stage+'.lean').write_text(src,encoding='utf-8')
print('Prepared seven actual central-subspace quotient stages; retained center sources unchanged.')
