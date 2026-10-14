import Hindman168.RoughVectorVariableRenaming
import Hindman168.RoughVectorSpatialAffineProjection

/-! Put EVERY original variable into the spatial coordinates, leaving the
new Option parameter unused. Original base variables are not frozen. -/
namespace Hindman168
open MvPolynomial
variable {σ τ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughVectorSpatialLift (f : σ → τ) (p : RoughVectorMvPolynomial σ E) :
    RoughVectorMvPolynomial (Option τ) E :=
  roughVectorMvRename Option.some (roughVectorMvRename f p)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem rough_vector_spatial_lift_degree (f : σ → τ) (p : RoughVectorMvPolynomial σ E)
    (k : ℕ) (hp : RoughVectorMvDegreeLE p k) :
    RoughVectorMvDegreeLE (roughVectorSpatialLift f p) k :=
  rough_vector_rename_degree Option.some (rough_vector_rename_degree f hp)

theorem rough_vector_spatial_lift_eval (f : σ → τ) (p : RoughVectorMvPolynomial σ E)
    (x : Option τ → ℝ) :
    roughVectorMvEval (roughVectorSpatialLift f p) x =
      roughVectorMvEval p (fun i => x (some (f i))) := by
  rw [roughVectorSpatialLift, rough_vector_rename_eval, rough_vector_rename_eval]
  rfl

theorem rough_vector_spatial_lift_projection (f : σ → τ) (p : RoughVectorMvPolynomial σ E)
    (chi : E →ₗ[ℝ] ℝ) (z : ℝ) :
    roughScalarSpatialProjection chi (roughVectorSpatialLift f p) z =
      rename f (roughVectorMvProjection chi p) := by
  unfold roughScalarSpatialProjection roughVectorSpatialLift
  rw [rough_vector_rename_projection, rough_vector_rename_projection,
    rough_spatial_rename_option_right, map_map]
  have he : (Polynomial.evalRingHom z).comp Polynomial.C = RingHom.id ℝ := by
    ext r
    exact Polynomial.eval_C
  rw [he, map_id]

theorem rough_vector_spatial_lift_coefficient (f : σ → τ) (hf : Function.Injective f)
    (p : RoughVectorMvPolynomial σ E) (chi : E →ₗ[ℝ] ℝ) (z : ℝ) (I : σ →₀ ℕ) :
    coeff (I.mapDomain f) (roughScalarSpatialProjection chi (roughVectorSpatialLift f p) z) =
      coeff I (roughVectorMvProjection chi p) := by
  rw [rough_vector_spatial_lift_projection, coeff_rename_mapDomain f hf]

end Hindman168
