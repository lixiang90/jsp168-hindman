import Hindman168.RoughSpatialAffineSubstitution

/-! Literal affine change of the Option parameter retains raw source,
ordinary degree and EVERY actual scalar spatial coefficient. -/
namespace Hindman168
open MvPolynomial
variable {κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughParameterAffineSource (a b : ℝ)
    (p : RoughVectorMvPolynomial (Option κ) E) : RoughVectorMvPolynomial (Option κ) E :=
  roughVectorMvAffineSubstitution (fun i => i.elim a (fun _ => 0)) (fun i => i.elim b (fun _ => 1)) p

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem rough_parameter_affine_degree (a b : ℝ) {p : RoughVectorMvPolynomial (Option κ) E}
    {d : ℕ} (hp : RoughVectorMvDegreeLE p d) :
    RoughVectorMvDegreeLE (roughParameterAffineSource a b p) d :=
  roughVectorMvAffineSubstitution_degree _ _ hp

theorem rough_parameter_affine_eval (a b z : ℝ) (y : κ → ℝ)
    (p : RoughVectorMvPolynomial (Option κ) E) :
    roughVectorMvEval (roughParameterAffineSource a b p) (fun i => i.elim z y) =
      roughVectorMvEval p (fun i => i.elim (a+b*z) y) := by
  rw [roughParameterAffineSource,roughVectorMvAffineSubstitution_eval]
  congr 1
  funext i
  cases i <;> simp

theorem rough_parameter_affine_specialize (a b z : ℝ) (p : MvPolynomial (Option κ) ℝ) :
    roughMvParameterSpecialize z
      (roughMvAffineSubstitution (fun i => i.elim a (fun _ => 0)) (fun i => i.elim b (fun _ => 1)) p) =
      roughMvParameterSpecialize (a+b*z) p := by
  have he : (roughMvParameterSpecialize (κ := κ) z).comp
      (roughMvAffineSubstitution (fun i => i.elim a (fun _ => 0)) (fun i => i.elim b (fun _ => 1))) =
      roughMvParameterSpecialize (a+b*z) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply,roughMvParameterSpecialize,roughMvAffineSubstitution]
    · intro i
      cases i <;> simp [RingHom.comp_apply,roughMvParameterSpecialize,roughMvAffineSubstitution]
  exact congrArg (fun f => f p) he

theorem rough_parameter_affine_spatial_projection (χ : E →ₗ[ℝ] ℝ)
    (a b z : ℝ) (p : RoughVectorMvPolynomial (Option κ) E) :
    roughScalarSpatialProjection χ (roughParameterAffineSource a b p) z =
      roughScalarSpatialProjection χ p (a+b*z) := by
  have h (q : RoughVectorMvPolynomial (Option κ) E) (r : ℝ) :
      roughScalarSpatialProjection χ q r = roughMvParameterSpecialize r (roughVectorMvProjection χ q) := by
    rw [rough_mv_parameter_specialize_option_right]
    rfl
  rw [h,roughParameterAffineSource,rough_vector_projection_affine_substitution,
    rough_parameter_affine_specialize,h]

end Hindman168
