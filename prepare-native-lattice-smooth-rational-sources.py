from pathlib import Path

for old_name, new_name in [
    ('NativeLatticeOrderedRationalBasis', 'NativeLatticeOrderedSmoothRationalBasis'),
    ('NativeLatticeOrderedBasisCoordinates', 'NativeLatticeOrderedSmoothBasisCoordinates')
]:
    src = Path('Hindman168/'+old_name+'.lean').read_text(encoding='utf-8')
    src = src.replace('import Hindman168.NativeLatticeOrderedRealBasis',
                      'import Hindman168.NativeLatticeOrderedDiffeomorph')
    src = src.replace('NativeLatticeOrderedRationalBasis', 'NativeLatticeOrderedSmoothRationalBasis')
    src = src.replace('nativeLatticeOrderedRational', 'nativeLatticeOrderedSmoothRational')
    src = src.replace('nativeLatticeOrderedRealBasis', 'nativeLatticeOrderedSmoothRealBasis')
    src = src.replace('native_lattice_ordered_rational', 'native_lattice_ordered_smooth_rational')
    src = src.replace('native_lattice_ordered_basis', 'native_lattice_ordered_smooth_basis')
    src = src.replace('native_lattice_ordered_differential', 'native_lattice_ordered_smooth_differential')
    Path('Hindman168/'+new_name+'.lean').write_text(src, encoding='utf-8')
    print('Prepared', new_name)
