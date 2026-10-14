from pathlib import Path
src=Path('Hindman168/NativeOriginalBadPairCharacters.lean').read_text(encoding='utf-8')
start=src.index('theorem native_original_bad_pair_characters')
stop=src.index(' := by',start)
header=src[start:stop].replace('native_original_bad_pair_characters','native_original_real_bad_pair_characters').replace('RoughNativeComplexBadIndex','RoughNativeBadIndex')
result='''import Hindman168.NativeOriginalBadPairCharacters
import Hindman168.RoughNativeRealBadIndexComplex

/-! ACTUAL real bad pairs retain EXACT original discrepancy in the proved
complex production theorem; ALL original affine rows and fixed budget survive. -/
namespace Hindman168
open MeasureTheory MvPolynomial
open scoped Manifold ContDiff BigOperators Classical
universe u

'''+header+''' := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨S,hS,A,Z0,hA,hZ0,hProduce⟩ := native_original_bad_pair_characters D n d c C B η L hc hC hB hη
  refine ⟨S,hS,A,Z0,hA,hZ0,?_⟩
  intro t ht Z hZ hZt htZ htc Q p hp hQ z hBad
  exact hProduce t ht Z hZ hZt htZ htc Q p hp hQ z
    (rough_native_real_bad_index_complex D Q z t Z c C L B η hBad)

end Hindman168
'''
Path('Hindman168/NativeOriginalRealBadPairCharacters.lean').write_text(result,encoding='utf-8')
