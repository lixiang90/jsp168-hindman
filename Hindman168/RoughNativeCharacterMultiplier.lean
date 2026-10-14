import Hindman168.RoughNativeScalarExpansion
import Hindman168.RoughBinomialCubeScale

namespace Hindman168
open MvPolynomial
open scoped Manifold ContDiff Classical
attribute [local instance] lieGroup_smooth_min_three

theorem rough_vector_projection_smul {σ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (χ : E →ₗ[ℝ] ℝ)
    (p : RoughVectorMvPolynomial σ E) (M : ℝ) :
    roughVectorMvProjection (M • χ) p = C M*roughVectorMvProjection χ p := by
  induction p with
  | nil => simp [roughVectorMvProjection]
  | cons a p ih =>
    simp only [roughVectorMvProjection, LinearMap.smul_apply, smul_eq_mul, map_mul, ih]
    ring

theorem rough_scalar_spatial_projection_smul {κ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (χ : E →ₗ[ℝ] ℝ)
    (p : RoughVectorMvPolynomial (Option κ) E) (z M : ℝ) :
    roughScalarSpatialProjection (M • χ) p z = C M*roughScalarSpatialProjection χ p z := by
  simp only [roughScalarSpatialProjection, rough_vector_projection_smul, map_mul,
    optionEquivRight_C, map_C]
  rw [Polynomial.evalRingHom]
  simp only [Polynomial.coe_eval₂RingHom, RingHom.id_apply, Polynomial.eval₂_C]

theorem rough_native_integer_character_multiple {step : ℕ}
    (D : NativeNilmanifoldData step) (χ : D.E →ₗ[ℝ] ℝ) (M : ℕ)
    (hΓ : ∀ g ∈ D.Γ, ∃ n : ℤ,
      nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ g = (n : ℝ)) :
    ∀ g ∈ D.Γ, ∃ n : ℤ,
      nativeLieLogarithmCharacter (I := D.I) (G := D.G) ((M : ℝ) • χ) g = (n : ℝ) := by
  intro g hg
  obtain ⟨n, hn⟩ := hΓ g hg
  refine ⟨(M : ℤ)*n, ?_⟩
  change (M : ℝ)*nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ g = _
  rw [hn, Int.cast_mul, Int.cast_natCast]

theorem rough_integer_character_multiple_nonzero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (χ : E →ₗ[ℝ] ℝ)
    (M : ℕ) (hM : 0 < M) (v : E) (hv : χ v ≠ 0) :
    ((M : ℝ) • χ) v ≠ 0 := by
  simp only [LinearMap.smul_apply, smul_eq_mul]
  exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hM) hv

end Hindman168
