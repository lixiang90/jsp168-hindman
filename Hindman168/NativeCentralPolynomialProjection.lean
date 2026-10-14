import Hindman168.NativeCentralCharacterGrid
import Hindman168.RoughVectorMvProjectionNaturality
import Hindman168.CentralFactorCosetMap

/-! Original logarithmic-polynomial orbit maps to the actual CHILD orbit,
with degree retained and exact scalar polynomials/coefficient identities. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeMvPolynomialOrbit {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (x : σ → ℤ) : D.G ⧸ D.Γ :=
  (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (roughVectorMvEval (E := D.E) p (fun i => (x i : ℝ))) : D.G ⧸ D.Γ)

noncomputable def nativeCentralPolynomialProjection {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) :
    RoughVectorMvPolynomial σ (nativeCentralQuotientData D).E :=
  roughVectorMvLinearMap (nativeCenterQuotientProjection (I := D.I) (G := D.G)).toLinearMap p

theorem native_central_polynomial_projection_degree {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (d : ℕ)
    (hp : RoughVectorMvDegreeLE p d) :
    RoughVectorMvDegreeLE (nativeCentralPolynomialProjection D p) d :=
  roughVectorMvLinearMap_degree _ hp

theorem native_central_polynomial_projection_eval {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (x : σ → ℝ) :
    roughVectorMvEval (nativeCentralPolynomialProjection D p) x =
      nativeCenterQuotientProjection (I := D.I) (G := D.G) (roughVectorMvEval p x) :=
  roughVectorMvLinearMap_eval _ p x

theorem native_central_polynomial_projection_orbit {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (x : σ → ℤ) :
    centralFactorCosetMap D.Γ (nativeMvPolynomialOrbit D p x) =
      nativeMvPolynomialOrbit (nativeCentralQuotientData D) (nativeCentralPolynomialProjection D p) x := by
  unfold nativeMvPolynomialOrbit
  rw [central_factor_coset_map_mk, native_central_polynomial_projection_eval]
  exact congrArg (fun g : (nativeCentralQuotientData D).G =>
    (g : (nativeCentralQuotientData D).G ⧸ (nativeCentralQuotientData D).Γ))
      (native_central_quotient_data_exponential D (roughVectorMvEval p (fun i => (x i : ℝ))))

theorem native_central_polynomial_projection_log_representation {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E)
    (P : (σ → ℝ) → D.G)
    (hP : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) (P x))
    (x : σ → ℝ) :
    roughVectorMvEval (nativeCentralPolynomialProjection D p) x =
      nativeLieGlobalLogarithm (E := (nativeCentralQuotientData D).E)
        (I := (nativeCentralQuotientData D).I) (G := (nativeCentralQuotientData D).G)
          (P x : D.G ⧸ Subgroup.center D.G) := by
  rw [native_central_polynomial_projection_eval, hP, native_central_quotient_data_logarithm]

theorem native_central_polynomial_projection_scalar {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E)
    (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ) :
    roughVectorMvProjection χ.toLinearMap (nativeCentralPolynomialProjection D p) =
      roughVectorMvProjection (nativeCentralCharacterPullback D χ).toLinearMap p :=
  roughVectorMvProjection_linearMap _ χ.toLinearMap p

theorem native_central_polynomial_projection_coeff {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E)
    (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ) (J : σ →₀ ℕ) :
    MvPolynomial.coeff J (roughVectorMvProjection χ.toLinearMap (nativeCentralPolynomialProjection D p)) =
      MvPolynomial.coeff J (roughVectorMvProjection (nativeCentralCharacterPullback D χ).toLinearMap p) := by
  rw [native_central_polynomial_projection_scalar]

end Hindman168
