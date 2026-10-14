from pathlib import Path

source = Path('Hindman168/NativeRationalDensePaperSeparation.lean').read_text(encoding='utf-8')
signature = source.split('theorem native_rational_dense_paper_separation',1)[1].split(' := by',1)[0]
signature = signature.replace('{s ℓ : ℕ}','{s : ℕ}').replace(' (hdeg : 2 ≤ ℓ)','')
a = signature.index('    (hInverse :')
b = signature.index('    (k :',a)
signature = (signature[:a]+signature[b:]).replace('ℓ','2')
body = ''' := by
  exact native_rational_dense_paper_separation D L (by omega)
    (native_rational_weighted_inverse_degree_one (nativeRationalDegreeReducedData D L)
      (nativeDegreeReducedRationalLieFiltration D L) Unit) k hk δ hδ hδ1
'''
target = '''import Hindman168.NativeRationalDensePaperSeparation

/-! Complete ACTUAL degree-two paper scalar separation with NO child inverse
premise. Bracket alternative/original nonzero inverse remain unproved. -/
namespace Hindman168
open MeasureTheory Polynomial
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_degree_two_dense_paper_separation'''+signature+body+'\nend Hindman168\n'
Path('Hindman168/NativeRationalDegreeTwoDensePaperSeparation.lean').write_text(target,encoding='utf-8')
