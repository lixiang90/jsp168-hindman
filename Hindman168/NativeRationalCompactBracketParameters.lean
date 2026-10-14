import Hindman168.ScalarFractionalBracket
import Hindman168.NativeRationalCommutatorCoefficientBound

/-! Parameters of the SAME actual compact normalized source and SAME
natural common multiplier, including the true integer-offset beta correction. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalCompactBracketFrequency {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) : NativeRationalFirstLayerIndex D L → ℝ :=
  nativeRationalFirstLayerCoordinates D L
    (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1)

noncomputable def nativeRationalCompactBracketCoefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (M : ℕ) :
    NativeRationalFirstLayerIndex D L → ℝ :=
  fun i => (M : ℝ)*nativeRationalCommutatorFirstLayerCoefficient D L χ
    (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1) i

noncomputable def nativeRationalCompactBracketBeta {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (M : ℕ)
    (b : NativeRationalFirstLayerIndex D L → ℤ) : ℝ :=
  (M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).eval 1+
    ∑ i, nativeRationalCompactBracketCoefficient D L p χ M i*(b i : ℝ)

noncomputable def nativeRationalCompactBracketAlpha {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (M : ℕ) : ℝ :=
  (M : ℝ)*scalarPolynomialBinomialCoefficient (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ 2

theorem native_rational_compact_bracket_frequency_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (p : RoughVectorMvPolynomial Unit D.E), ∀ i,
      |nativeRationalCompactBracketFrequency D L p i| ≤ H := by
  obtain ⟨H,hH,hbound⟩ := native_rational_first_layer_representative_bound D L
  refine ⟨H,hH,?_⟩
  intro p i
  unfold nativeRationalCompactBracketFrequency
  rw [native_rational_compact_normalized_polynomial_one]
  exact hbound _ (native_rational_representative_mem D _) i

theorem native_rational_compact_bracket_coefficient_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (A : ℝ) (hA : 0 ≤ A) (S : ℕ) :
    ∃ Z : ℝ, 0 ≤ Z ∧ ∀ (p : RoughVectorMvPolynomial Unit D.E)
      (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ), ‖χ‖ ≤ A →
      ∀ M : ℕ, M ≤ S → ∀ i, |nativeRationalCompactBracketCoefficient D L p χ M i| ≤ Z := by
  obtain ⟨B,hB,hbound⟩ := native_rational_compact_commutator_coefficient_bound D L
  refine ⟨(S : ℝ)*A*B,by positivity,?_⟩
  intro p χ hχ M hM i
  have hmr : (M : ℝ) ≤ S := by exact_mod_cast hM
  change |(M : ℝ)*_| ≤ _
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg M)]
  calc
    _ ≤ (M : ℝ)*(‖χ‖*B) := mul_le_mul_of_nonneg_left (hbound p χ i) (Nat.cast_nonneg M)
    _ ≤ (S : ℝ)*(A*B) := mul_le_mul hmr (mul_le_mul_of_nonneg_right hχ hB)
      (mul_nonneg (norm_nonneg χ) hB) (Nat.cast_nonneg S)
    _ = _ := by ring

end Hindman168
