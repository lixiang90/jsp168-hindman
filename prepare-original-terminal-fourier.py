from pathlib import Path
import re

for old,new in [
    ('NativeCentralOrbitObservables','NativeOriginalTerminalOrbitObservables'),
    ('NativeCentralFourierProjection','NativeOriginalTerminalFourierProjection'),
    ('NativeCentralFourierReconstruction','NativeOriginalTerminalFourierReconstruction'),
    ('NativeCentralFourierSelection','NativeOriginalTerminalFourierSelection'),
    ('NativeCentralFourierCompactFamilies','NativeOriginalTerminalFourierCompactFamilies'),
]:
    p = Path('Hindman168/'+old+'.lean')
    source = p.read_text(encoding='utf-8')
    source = source.replace('Hindman168.NativeNilmanifoldCentralAction','Hindman168.NativeOriginalTerminalAction')
    source = source.replace('Hindman168.NativeCentralOrbitObservables','Hindman168.NativeOriginalTerminalOrbitObservables')
    source = source.replace('Hindman168.NativeCentralFourierProjection','Hindman168.NativeOriginalTerminalFourierProjection')
    source = source.replace('Hindman168.NativeCentralFourierReconstruction','Hindman168.NativeOriginalTerminalFourierReconstruction')
    if old == 'NativeCentralFourierSelection':
        source = source.replace('import Hindman168.NativeNilmanifoldFiniteDiscrepancy',
          'import Hindman168.NativeOriginalTerminalDiscrepancy')
        source = source.replace('native_nilmanifold_finite_discrepancy_nonzero_projection D',
          'native_nilmanifold_finite_discrepancy_nonzero_terminal_projection D d hd')
    source = source.replace('nativeCentralOrbitObservable','nativeOriginalTerminalOrbitObservable')
    source = source.replace('nativeCentralFourierProjection','nativeOriginalTerminalFourierProjection')
    source = source.replace('nativeNilmanifoldCentralAction','nativeOriginalTerminalAction')
    source = source.replace('nativeNilmanifoldCenterIndex D','nativeOriginalTerminalIndex D d')
    source = source.replace('native_nilmanifold_central_action_','native_original_terminal_action_')
    source = source.replace('native_central_','native_original_terminal_')
    source = source.replace('(D : NativeNilmanifoldData.{u} s)',
      '(D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)')
    source = re.sub(r'(native_original_terminal_[A-Za-z0-9_]+) D\b',r'\1 D d hd',source)
    for name in ['nativeOriginalTerminalOrbitObservable','nativeOriginalTerminalFourierProjection','nativeOriginalTerminalAction']:
        source = source.replace(name+' D',name+' D d hd')
    source = source.replace('/-!','/-! ACTUAL ORIGINAL TERMINAL-LAYER specialization. All action inputs are\nproved from original terminal centrality/rationality/lattice coordinates.\n',1)
    target = Path('Hindman168/'+new+'.lean')
    if not target.exists():
        target.write_text(source,encoding='utf-8')
        print('Prepared '+new)
    else:
        print('Retained existing '+new)
