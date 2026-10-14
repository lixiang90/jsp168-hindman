import Hindman168.NativeSubgroupHorizontalLevelBridge
import Hindman168.RoughVectorZeroTrimProjection

/-! Exact bounded-degree logarithmic source for the actual initial subgroup.
Zero vector terms are removed before invoking the ordinary-degree inverse.
The full projected polynomial, including all coefficients, is unchanged. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalLayerLogPolynomial {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) :
    RoughVectorMvPolynomial σ (F.layer 0) :=
  roughNativeSubgroupLogPolynomial (nativeRationalSubgroupLayerAlgebra D F 0)
    (roughVectorMvZeroTrim p)

theorem native_rational_layer_log_polynomial_degree {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughVectorMvDegreeLE (nativeRationalLayerLogPolynomial D F p) ℓ := by
  apply roughNativeSubgroupLogPolynomial_degree
  simpa only [Nat.sub_zero] using
    rough_vector_zero_trim_degree F.layer F.antitone hp F.terminal

theorem native_rational_layer_log_polynomial_log {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (x : σ → ℝ) :
    let A := nativeRationalLayerOrbitData D F 0 rho hRat
    nativeLieGlobalLogarithm (E := A.E) (I := A.I) (G := A.G)
      (nativeRationalSubgroupPolynomialOrbit D F p hp x) =
      roughVectorMvEval (nativeRationalLayerLogPolynomial D F p) x := by
  dsimp only
  symm
  apply roughNativeSubgroupLogPolynomial_eval
  intro y
  rw [rough_vector_zero_trim_eval, native_rational_subgroup_polynomial_orbit_logarithm]

theorem native_rational_layer_log_polynomial_projection {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (p : RoughVectorMvPolynomial σ D.E)
    (chi : (nativeRationalLayerOrbitData D F 0 rho hRat).E →ₗ[ℝ] ℝ) :
    roughVectorMvProjection chi (nativeRationalLayerLogPolynomial D F p) =
      roughVectorMvProjection (nativeSubgroupHorizontalExtension D F rho hRat chi) p := by
  change F.layer 0 →ₗ[ℝ] ℝ at chi
  apply MvPolynomial.funext
  intro x
  rw [roughVectorMvProjection_eval, roughVectorMvProjection_eval]
  change chi (roughVectorMvEval (roughVectorMvLinearMap
    (finiteRealSubmoduleRetraction (F.layer 0)).toLinearMap (roughVectorMvZeroTrim p)) x) = _
  exact congrArg chi ((roughVectorMvLinearMap_eval
    (finiteRealSubmoduleRetraction (F.layer 0)).toLinearMap (roughVectorMvZeroTrim p) x).trans
    (congrArg (finiteRealSubmoduleRetraction (F.layer 0)) (rough_vector_zero_trim_eval p x)))

end Hindman168
