import Hindman168.NativeRationalTerminalCharacterGrid
import Hindman168.NativeRationalTerminalPolynomial
import Hindman168.RoughVectorZeroTrimProjection
import Hindman168.MvBinomialDegreeExtension

/-! COMPLETE original scalar coefficients and paper-binomial coefficients
are retained by ACTUAL quotient character pullback, including zero trimming
and the genuine increase from child degree ell-1 to parent degree ell. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_terminal_character_pullback_scalar {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ) (p : RoughVectorMvPolynomial σ D.E) :
    roughVectorMvProjection (nativeRationalTerminalCharacterPullback D L χ).toLinearMap p =
      roughVectorMvProjection χ.toLinearMap (nativeRationalTerminalPolynomial D L p) :=
  (native_rational_terminal_polynomial_scalar D L p χ.toLinearMap).symm

theorem native_rational_terminal_character_pullback_zero_trim_scalar {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ) (p : RoughVectorMvPolynomial σ D.E) :
    roughVectorMvProjection (nativeRationalTerminalCharacterPullback D L χ).toLinearMap p =
      roughVectorMvProjection χ.toLinearMap (roughVectorMvZeroTrim (nativeRationalTerminalPolynomial D L p)) :=
  (native_rational_terminal_character_pullback_scalar D L χ p).trans (rough_vector_zero_trim_projection χ.toLinearMap _).symm

theorem native_rational_terminal_character_pullback_coefficient {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ) (p : RoughVectorMvPolynomial σ D.E) (J : σ →₀ ℕ) :
    MvPolynomial.coeff J (roughVectorMvProjection (nativeRationalTerminalCharacterPullback D L χ).toLinearMap p) =
      MvPolynomial.coeff J (roughVectorMvProjection χ.toLinearMap (roughVectorMvZeroTrim (nativeRationalTerminalPolynomial D L p))) := by
  rw [native_rational_terminal_character_pullback_zero_trim_scalar]

theorem native_rational_terminal_character_pullback_scalar_degree {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ) {p : RoughVectorMvPolynomial σ D.E}
    (hp : RoughVectorMvWeightedDegree L.layer p 0) :
    (roughVectorMvProjection (nativeRationalTerminalCharacterPullback D L χ).toLinearMap p).totalDegree ≤ ℓ-1 := by
  rw [native_rational_terminal_character_pullback_zero_trim_scalar]
  exact roughVectorMvProjection_degree _ (native_rational_terminal_polynomial_zero_trim_degree D L hp)

theorem native_rational_terminal_character_pullback_binomial {s ℓ : ℕ} {σ : Type*} [Fintype σ]
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ) {p : RoughVectorMvPolynomial σ D.E}
    (hp : RoughVectorMvWeightedDegree L.layer p 0) (J : σ → ℕ) :
    mvPolynomialBinomialCoefficient (roughVectorMvProjection (nativeRationalTerminalCharacterPullback D L χ).toLinearMap p) ℓ J =
      mvPolynomialBinomialCoefficient (roughVectorMvProjection χ.toLinearMap
        (roughVectorMvZeroTrim (nativeRationalTerminalPolynomial D L p))) (ℓ-1) J := by
  rw [mv_binomial_coefficient_degree_extension _ (ℓ-1) ℓ (Nat.sub_le _ _)
    (native_rational_terminal_character_pullback_scalar_degree D L χ hp),
    native_rational_terminal_character_pullback_zero_trim_scalar]

end Hindman168
