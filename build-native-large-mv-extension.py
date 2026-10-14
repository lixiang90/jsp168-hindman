from pathlib import Path
import re

src = Path('Hindman168/NativeRationalLargeToAllLengths.lean').read_text(encoding='utf-8')
src = src.replace('NativeRationalConstantDiscrepancyAnchor', 'NativeRationalConstantMvDiscrepancyAnchor')
src = src.replace('native_rational_large_inverse_to_all_lengths', 'native_rational_large_mv_inverse_to_all_lengths')
src = src.replace('{s ℓ : ℕ}', '{s ℓ : ℕ} {σ : Type*} [Fintype σ]')
src = re.sub(r'\bUnit\b', 'σ', src)
src = src.replace('nativeRationalConstantPolynomial', 'nativeRationalConstantMvPolynomial σ')
src = src.replace('native_rational_constant_polynomial_weighted', 'native_rational_constant_mv_polynomial_weighted')
src = src.replace('native_rational_constant_discrepancy_anchor', 'native_rational_constant_mv_discrepancy_anchor')
Path('Hindman168/NativeRationalLargeMvToAllLengths.lean').write_text(src, encoding='utf-8')
