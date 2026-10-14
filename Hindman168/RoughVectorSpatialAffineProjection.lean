import Hindman168.RoughVectorParameterSpecialization
import Hindman168.RoughNativeScalarExpansion

namespace Hindman168
open MvPolynomial

theorem rough_mv_parameter_specialize_option_right {κ : Type*} (z : ℝ) :
    roughMvParameterSpecialize (κ := κ) z =
      (MvPolynomial.map (Polynomial.evalRingHom z)).comp (optionEquivRight ℝ κ).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change eval₂ C _ (C r) = map (Polynomial.evalRingHom z) (optionEquivRight ℝ κ (C r))
    rw [eval₂_C, optionEquivRight_C, map_C]
    change C r = C (Polynomial.eval z (Polynomial.C r))
    rw [Polynomial.eval_C]
  · intro i
    cases i with
    | none =>
      change eval₂ C _ (X none) = map (Polynomial.evalRingHom z) (optionEquivRight ℝ κ (X none))
      rw [eval₂_X, optionEquivRight_X_none, map_C]
      change C z = C (Polynomial.eval z Polynomial.X)
      rw [Polynomial.eval_X]
    | some i =>
      change eval₂ C _ (X (some i)) = map (Polynomial.evalRingHom z) (optionEquivRight ℝ κ (X (some i)))
      rw [eval₂_X, optionEquivRight_X_some, map_X]
      rfl

variable {κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rough_vector_projection_parameter_specialize (χ : E →ₗ[ℝ] ℝ)
    (z : ℝ) (p : RoughVectorMvPolynomial (Option κ) E) :
    roughVectorMvProjection χ (roughVectorMvParameterSpecialize z p) =
      roughMvParameterSpecialize z (roughVectorMvProjection χ p) := by
  induction p with
  | nil => simp only [roughVectorMvParameterSpecialize, List.map_nil, roughVectorMvProjection, map_zero]
  | cons a p ih =>
    change roughMvParameterSpecialize z a.1 * C (χ a.2) +
      roughVectorMvProjection χ (roughVectorMvParameterSpecialize z p) = _
    rw [ih]
    simp only [roughVectorMvProjection, map_add, map_mul]
    simp only [roughMvParameterSpecialize, eval₂Hom_C]

theorem rough_vector_projection_affine_substitution (χ : E →ₗ[ℝ] ℝ)
    (u k : κ → ℝ) (p : RoughVectorMvPolynomial κ E) :
    roughVectorMvProjection χ (roughVectorMvAffineSubstitution u k p) =
      roughMvAffineSubstitution u k (roughVectorMvProjection χ p) := by
  induction p with
  | nil => simp only [roughVectorMvAffineSubstitution, List.map_nil, roughVectorMvProjection, map_zero]
  | cons a p ih =>
    change roughMvAffineSubstitution u k a.1 * C (χ a.2) +
      roughVectorMvProjection χ (roughVectorMvAffineSubstitution u k p) = _
    rw [ih]
    simp only [roughVectorMvProjection, map_add, map_mul]
    simp only [roughMvAffineSubstitution, eval₂Hom_C]

theorem rough_vector_spatial_affine_projection (χ : E →ₗ[ℝ] ℝ)
    (z : ℝ) (u k : κ → ℝ) (p : RoughVectorMvPolynomial (Option κ) E) :
    roughVectorMvProjection χ (roughVectorMvAffineSubstitution u k (roughVectorMvParameterSpecialize z p)) =
      roughMvAffineSubstitution u k (roughScalarSpatialProjection χ p z) := by
  rw [rough_vector_projection_affine_substitution, rough_vector_projection_parameter_specialize,
    rough_mv_parameter_specialize_option_right]
  rfl

end Hindman168
