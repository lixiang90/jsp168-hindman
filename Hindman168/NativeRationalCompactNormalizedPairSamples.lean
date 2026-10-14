import Hindman168.NativeRationalCompactNormalizedPolynomial

/-! ACTUAL compactly chosen normalized relative pair retains BOTH original
integer coset coordinates. The original lattice need not be normal. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalCompactNormalizedIntegerPair {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (h n : ℤ) :
    (nativeRationalRelativeData D F 1).G :=
  nativeRationalWeightedIntegerPair D F (nativeRationalCompactNormalizedPolynomial D p)
    (native_rational_compact_normalized_polynomial_weighted D F hp)
    (native_rational_compact_normalized_polynomial_zero D p) (nativeRationalShiftRepresentative D p h) h n

theorem native_rational_compact_pair_first_original_sample {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (h n : ℤ) :
    (nativeRationalBasepointRepresentative D p * nativeRationalShiftRepresentative D p h) •
      ((nativeRationalRelativeGroupInclusion D F 1 (nativeRationalCompactNormalizedIntegerPair D F p hp h n)).1 :
        D.G ⧸ D.Γ) = nativeMvPolynomialOrbit D p (fun _ => n+h) := by
  have he : nativeRationalShiftRepresentative D p h •
      ((nativeRationalRelativeGroupInclusion D F 1 (nativeRationalCompactNormalizedIntegerPair D F p hp h n)).1 :
        D.G ⧸ D.Γ) = nativeMvPolynomialOrbit D (nativeRationalCompactNormalizedPolynomial D p) (fun _ => n+h) :=
    rough_normalized_integer_pair_original_coset D.Γ
      (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p))
      (nativeRationalShiftRepresentative D p h) h n
      (nativeRationalRepresentativeLatticePart D
        (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1 ^ h))
      (native_rational_compact_shift_factorization D p h)
  rw [mul_smul,he]
  exact native_rational_compact_normalized_original_sample D p (fun _ => n+h)

theorem native_rational_compact_pair_second_original_sample {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (h n : ℤ) :
    nativeRationalBasepointRepresentative D p •
      ((nativeRationalRelativeGroupInclusion D F 1 (nativeRationalCompactNormalizedIntegerPair D F p hp h n)).2 :
        D.G ⧸ D.Γ) = nativeMvPolynomialOrbit D p (fun _ => n) := by
  change nativeRationalBasepointRepresentative D p •
    ((roughNormalizedIntegerPair (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p))
      (nativeRationalShiftRepresentative D p h) h n).2 : D.G ⧸ D.Γ) = _
  rw [rough_normalized_integer_pair_second]
  exact native_rational_compact_normalized_original_sample D p (fun _ => n)

theorem native_rational_compact_pair_original_observable_sample {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (h n : ℤ)
    (H : D.G ⧸ D.Γ → ℂ) :
    H ((nativeRationalBasepointRepresentative D p * nativeRationalShiftRepresentative D p h) •
      ((nativeRationalRelativeGroupInclusion D F 1 (nativeRationalCompactNormalizedIntegerPair D F p hp h n)).1 : D.G ⧸ D.Γ)) *
    star (H (nativeRationalBasepointRepresentative D p •
      ((nativeRationalRelativeGroupInclusion D F 1 (nativeRationalCompactNormalizedIntegerPair D F p hp h n)).2 : D.G ⧸ D.Γ))) =
    H (nativeMvPolynomialOrbit D p (fun _ => n+h)) * star (H (nativeMvPolynomialOrbit D p (fun _ => n))) := by
  rw [native_rational_compact_pair_first_original_sample,native_rational_compact_pair_second_original_sample]

end Hindman168
