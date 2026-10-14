import Hindman168.NativeRelativeReductionExponentialLogarithm
import Hindman168.NativeCentralPolynomialProjection
import Hindman168.RoughVectorMvProjectionNaturality

/-! SAME ACTUAL relative polynomial projects to SAME native terminal
quotient with degree/evaluations/orbit/log and COMPLETE scalar coefficients.
Original normalized-pair membership is not assumed proved by this transport. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRelativeReductionPolynomial {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial σ (nativeRelativeSquareData D d hd 1).E) :
    RoughVectorMvPolynomial σ (nativeRelativeReducedData D d hd).E :=
  roughVectorMvLinearMap (nativeRelativeReductionModelProjection D d hd).toLinearMap p

theorem native_relative_reduction_polynomial_degree {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial σ (nativeRelativeSquareData D d hd 1).E)
    (b : ℕ) (hp : RoughVectorMvDegreeLE p b) : RoughVectorMvDegreeLE (nativeRelativeReductionPolynomial D d hd p) b :=
  roughVectorMvLinearMap_degree _ hp

theorem native_relative_reduction_polynomial_eval {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial σ (nativeRelativeSquareData D d hd 1).E) (x : σ → ℝ) :
    roughVectorMvEval (nativeRelativeReductionPolynomial D d hd p) x =
      nativeRelativeReductionModelProjection D d hd (roughVectorMvEval p x) := roughVectorMvLinearMap_eval _ p x

theorem native_relative_reduction_polynomial_orbit {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial σ (nativeRelativeSquareData D d hd 1).E) (x : σ → ℤ) :
    nativeRelativeReductionFactorMap D d hd (nativeMvPolynomialOrbit (nativeRelativeSquareData D d hd 1) p x) =
      nativeMvPolynomialOrbit (nativeRelativeReducedData D d hd) (nativeRelativeReductionPolynomial D d hd p) x := by
  unfold nativeMvPolynomialOrbit
  change ((nativeRelativeReductionGroupProjection D d hd
    (nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G)
      (roughVectorMvEval (E := (nativeRelativeSquareData D d hd 1).E) p (fun i => (x i : ℝ))))) :
        (nativeRelativeReducedData D d hd).G ⧸ (nativeRelativeReducedData D d hd).Γ) = _
  rw [native_relative_reduction_data_exponential,native_relative_reduction_polynomial_eval]

theorem native_relative_reduction_polynomial_log_representation {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial σ (nativeRelativeSquareData D d hd 1).E)
    (P : (σ → ℝ) → (nativeRelativeSquareData D d hd 1).G)
    (hP : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G) (P x)) (x : σ → ℝ) :
    roughVectorMvEval (nativeRelativeReductionPolynomial D d hd p) x =
      nativeLieGlobalLogarithm (E := (nativeRelativeReducedData D d hd).E)
        (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)
        (nativeRelativeReductionGroupProjection D d hd (P x)) := by
  rw [native_relative_reduction_polynomial_eval,hP,native_relative_reduction_data_logarithm]

theorem native_relative_reduction_polynomial_scalar {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial σ (nativeRelativeSquareData D d hd 1).E)
    (χ : (nativeRelativeReducedData D d hd).E →L[ℝ] ℝ) :
    roughVectorMvProjection χ.toLinearMap (nativeRelativeReductionPolynomial D d hd p) =
      roughVectorMvProjection (χ.comp (nativeRelativeReductionModelProjection D d hd)).toLinearMap p :=
  roughVectorMvProjection_linearMap _ χ.toLinearMap p

theorem native_relative_reduction_polynomial_coeff {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial σ (nativeRelativeSquareData D d hd 1).E)
    (χ : (nativeRelativeReducedData D d hd).E →L[ℝ] ℝ) (J : σ →₀ ℕ) :
    MvPolynomial.coeff J (roughVectorMvProjection χ.toLinearMap (nativeRelativeReductionPolynomial D d hd p)) =
      MvPolynomial.coeff J (roughVectorMvProjection (χ.comp (nativeRelativeReductionModelProjection D d hd)).toLinearMap p) := by
  rw [native_relative_reduction_polynomial_scalar]

end Hindman168
