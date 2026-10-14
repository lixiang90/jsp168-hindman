from pathlib import Path

modules = ['NativeSmoothBasisCharacterIntegrality', 'NativeSmoothBasisIntegerCharacters',
           'NativeSmoothBasisIntegerCharacterGrid', 'NativeSmoothIntegerCharacterNormalization']
for old in modules:
    src = Path('Hindman168/'+old+'.lean').read_text(encoding='utf-8')
    src = src.replace('NativeLatticeOrderedDiffeomorph','NativeLatticeFilteredDiffeomorph')
    src = src.replace('NativeLatticeOrderedSmoothBasisCoordinates','NativeLatticeFilteredSmoothBasisCoordinates')
    src = src.replace('nativeLatticeOrderedDiffeomorph','nativeLatticeFilteredDiffeomorph')
    src = src.replace('nativeLatticeOrderedSmoothRealBasis','nativeLatticeFilteredSmoothRealBasis')
    src = src.replace('native_lattice_ordered_smooth','native_lattice_filtered_smooth')
    src = src.replace('native_lattice_ordered_diffeomorph','native_lattice_filtered_diffeomorph')
    src = src.replace('NativeSmooth','NativeFilteredSmooth')
    src = src.replace('nativeSmooth','nativeFilteredSmooth')
    src = src.replace('native_smooth','native_filtered_smooth')
    new = old.replace('NativeSmooth','NativeFilteredSmooth')
    Path('Hindman168/'+new+'.lean').write_text(src,encoding='utf-8')
print('Prepared four actual filtered-basis character proofs; retained basis choices unchanged.')
