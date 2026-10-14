import Hindman168.RoughVectorSpatialAffineProjection

/-! Literal spatial affine substitution keeps the Option parameter fixed.
Actual vector source/evaluation/projection identities, not sampled coset inference. -/
namespace Hindman168
open MvPolynomial
variable {κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rough_spatial_affine_specialize (b k : κ → ℝ) (z : ℝ)
    (p : MvPolynomial (Option κ) ℝ) :
    roughMvParameterSpecialize z
      (roughMvAffineSubstitution (fun i => i.elim 0 b) (fun i => i.elim 1 k) p) =
    roughMvAffineSubstitution b k (roughMvParameterSpecialize z p) := by
  have he : (roughMvParameterSpecialize z).comp
      (roughMvAffineSubstitution (fun i => i.elim 0 b) (fun i => i.elim 1 k)) =
      (roughMvAffineSubstitution b k).comp (roughMvParameterSpecialize z) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply,roughMvParameterSpecialize,roughMvAffineSubstitution]
    · intro i
      cases i <;> simp [RingHom.comp_apply,roughMvParameterSpecialize,roughMvAffineSubstitution]
  exact congrArg (fun f => f p) he

theorem rough_spatial_affine_vector_projection (χ : E →ₗ[ℝ] ℝ)
    (b k : κ → ℝ) (p : RoughVectorMvPolynomial (Option κ) E) (z : ℝ) :
    roughScalarSpatialProjection χ
      (roughVectorMvAffineSubstitution (fun i => i.elim 0 b) (fun i => i.elim 1 k) p) z =
      roughMvAffineSubstitution b k (roughScalarSpatialProjection χ p z) := by
  have h (q : RoughVectorMvPolynomial (Option κ) E) :
      roughScalarSpatialProjection χ q z = roughMvParameterSpecialize z (roughVectorMvProjection χ q) := by
    rw [rough_mv_parameter_specialize_option_right]
    rfl
  rw [h,rough_vector_projection_affine_substitution,rough_spatial_affine_specialize,h]

theorem rough_spatial_affine_vector_eval (b k x : κ → ℝ)
    (p : RoughVectorMvPolynomial (Option κ) E) (z : ℝ) :
    roughVectorMvEval
      (roughVectorMvAffineSubstitution (fun i => i.elim 0 b) (fun i => i.elim 1 k) p)
      (fun i => i.elim z x) = roughVectorMvEval p (fun i => i.elim z (fun j => b j+k j*x j)) := by
  rw [roughVectorMvAffineSubstitution_eval]
  congr 1
  funext i
  cases i <;> simp

end Hindman168
