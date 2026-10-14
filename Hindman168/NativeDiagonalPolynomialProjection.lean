import Hindman168.NativeDiagonalQuotientProjection
import Hindman168.NativeCentralPolynomialProjection
import Hindman168.RoughVectorMvProjectionNaturality

/-! ACTUAL original product polynomial projects to ACTUAL native diagonal
polynomial with degree, all original samples and COMPLETE scalar coefficients. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeDiagonalPolynomialProjection {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ (nativeNilmanifoldProduct D D).E) :
    RoughVectorMvPolynomial σ (nativeDiagonalQuotientData D).E :=
  roughVectorMvLinearMap (nativeDiagonalModelProjection D).toLinearMap p

theorem native_diagonal_polynomial_projection_degree {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ (nativeNilmanifoldProduct D D).E)
    (d : ℕ) (hp : RoughVectorMvDegreeLE p d) : RoughVectorMvDegreeLE (nativeDiagonalPolynomialProjection D p) d :=
  roughVectorMvLinearMap_degree _ hp

theorem native_diagonal_polynomial_projection_eval {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ (nativeNilmanifoldProduct D D).E) (x : σ → ℝ) :
    roughVectorMvEval (nativeDiagonalPolynomialProjection D p) x =
      nativeDiagonalModelProjection D (roughVectorMvEval p x) := roughVectorMvLinearMap_eval _ p x

theorem native_diagonal_polynomial_projection_orbit {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ (nativeNilmanifoldProduct D D).E) (x : σ → ℤ) :
    nativeDiagonalFactorMap D (nativeMvPolynomialOrbit (nativeNilmanifoldProduct D D) p x) =
      nativeMvPolynomialOrbit (nativeDiagonalQuotientData D) (nativeDiagonalPolynomialProjection D p) x := by
  unfold nativeMvPolynomialOrbit
  change ((nativeDiagonalGroupProjection D (nativeLieExponential (E := (nativeNilmanifoldProduct D D).E)
    (I := (nativeNilmanifoldProduct D D).I) (G := (nativeNilmanifoldProduct D D).G)
      (roughVectorMvEval (E := (nativeNilmanifoldProduct D D).E) p (fun i => (x i : ℝ))))) :
        (nativeDiagonalQuotientData D).G ⧸ (nativeDiagonalQuotientData D).Γ) = _
  rw [native_diagonal_quotient_data_exponential,native_diagonal_polynomial_projection_eval]

theorem native_diagonal_polynomial_projection_log_representation {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ (nativeNilmanifoldProduct D D).E)
    (P : (σ → ℝ) → (nativeNilmanifoldProduct D D).G)
    (hP : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := (nativeNilmanifoldProduct D D).E)
      (I := (nativeNilmanifoldProduct D D).I) (G := (nativeNilmanifoldProduct D D).G) (P x)) (x : σ → ℝ) :
    roughVectorMvEval (nativeDiagonalPolynomialProjection D p) x =
      nativeLieGlobalLogarithm (E := (nativeDiagonalQuotientData D).E)
        (I := (nativeDiagonalQuotientData D).I) (G := (nativeDiagonalQuotientData D).G)
          (nativeDiagonalGroupProjection D (P x)) := by
  rw [native_diagonal_polynomial_projection_eval,hP,native_diagonal_quotient_data_logarithm]

theorem native_diagonal_polynomial_projection_scalar {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ (nativeNilmanifoldProduct D D).E)
    (χ : (nativeDiagonalQuotientData D).E →L[ℝ] ℝ) :
    roughVectorMvProjection χ.toLinearMap (nativeDiagonalPolynomialProjection D p) =
      roughVectorMvProjection (χ.comp (nativeDiagonalModelProjection D)).toLinearMap p :=
  roughVectorMvProjection_linearMap _ χ.toLinearMap p

theorem native_diagonal_polynomial_projection_coeff {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ (nativeNilmanifoldProduct D D).E)
    (χ : (nativeDiagonalQuotientData D).E →L[ℝ] ℝ) (J : σ →₀ ℕ) :
    MvPolynomial.coeff J (roughVectorMvProjection χ.toLinearMap (nativeDiagonalPolynomialProjection D p)) =
      MvPolynomial.coeff J (roughVectorMvProjection (χ.comp (nativeDiagonalModelProjection D)).toLinearMap p) := by
  rw [native_diagonal_polynomial_projection_scalar]

end Hindman168
