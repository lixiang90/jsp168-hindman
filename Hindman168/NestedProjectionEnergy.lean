import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The Hilbert-space identities used in the paper's gap-energy selection.
The subspaces and projections here are genuine orthogonal projections;
identifying the paper's nilsequence spaces is separate work. -/

namespace Hindman168

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

theorem nested_projection_energy_identity (hUV : U ≤ V) (x : E) :
    ‖V.starProjection x - U.starProjection x‖ ^ 2 =
      ‖V.starProjection x‖ ^ 2 - ‖U.starProjection x‖ ^ 2 := by
  have hp : U.starProjection (V.starProjection x) = U.starProjection x :=
    DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le hUV) x
  have h := U.norm_sq_eq_add_norm_sq_starProjection (V.starProjection x)
  simp only [Submodule.starProjection_orthogonal, sub_apply,
    ContinuousLinearMap.id_apply, hp] at h
  linarith

theorem nested_projection_energy_mono (hUV : U ≤ V) (x : E) :
    ‖U.starProjection x‖ ^ 2 ≤ ‖V.starProjection x‖ ^ 2 := by
  have h := nested_projection_energy_identity U V hUV x
  nlinarith [sq_nonneg ‖V.starProjection x - U.starProjection x‖]

theorem nested_projection_distance_le (hUV : U ≤ V) (x : E) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hgap : ‖V.starProjection x‖ ^ 2 - ‖U.starProjection x‖ ^ 2 ≤ ε ^ 2) :
    ‖V.starProjection x - U.starProjection x‖ ≤ ε := by
  rw [← nested_projection_energy_identity U V hUV x] at hgap
  nlinarith [norm_nonneg (V.starProjection x - U.starProjection x)]

theorem nested_projection_model_error (hUV : U ≤ V) (x s : E) (hs : s ∈ U)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hgap : ‖V.starProjection x‖ ^ 2 - ‖U.starProjection x‖ ^ 2 ≤ ε ^ 2)
    (happrox : ‖U.starProjection x - s‖ ≤ ε) :
    ‖V.starProjection (x - s)‖ ≤ 2 * ε := by
  rw [map_sub, Submodule.starProjection_eq_self_iff.mpr (hUV hs)]
  calc
    ‖V.starProjection x - s‖ ≤
        ‖V.starProjection x - U.starProjection x‖ + ‖U.starProjection x - s‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε + ε := add_le_add (nested_projection_distance_le U V hUV x hε hgap) happrox
    _ = 2 * ε := by ring

omit [V.HasOrthogonalProjection] in
theorem projection_pythagoras_of_mem (x s : E) (hs : s ∈ U) :
    ‖x - s‖ ^ 2 = ‖x - U.starProjection x‖ ^ 2 + ‖U.starProjection x - s‖ ^ 2 := by
  have h := U.norm_sq_eq_add_norm_sq_starProjection (x - s)
  simp only [Submodule.starProjection_orthogonal, sub_apply,
    ContinuousLinearMap.id_apply, map_sub, Submodule.starProjection_eq_self_iff.mpr hs,
    sub_self, sub_zero] at h
  linarith

omit [V.HasOrthogonalProjection] in
theorem projection_clipping_distance_le (x t s : E) (ht : t ∈ U) (hs : s ∈ U)
    (hclip : ‖x - s‖ ≤ ‖x - t‖) :
    ‖U.starProjection x - s‖ ≤ ‖U.starProjection x - t‖ := by
  have ht' := projection_pythagoras_of_mem U x t ht
  have hs' := projection_pythagoras_of_mem U x s hs
  have hsq := mul_self_le_mul_self (norm_nonneg (x - s)) hclip
  nlinarith [norm_nonneg (U.starProjection x - s), norm_nonneg (U.starProjection x - t)]

omit [V.HasOrthogonalProjection] in
theorem projection_clipped_representative_exists (x : E) (R : Set E)
    (hR : R ⊆ (U : Set E)) (hdense : (U : Set E) ⊆ closure R)
    (clip : E → E) (hclipR : ∀ t ∈ R, clip t ∈ R)
    (hcontract : ∀ t ∈ R, ‖x - clip t‖ ≤ ‖x - t‖)
    (Q : E → Prop) (hQ : ∀ t ∈ R, Q (clip t)) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ R, Q s ∧ ‖U.starProjection x - s‖ < ε := by
  have hp : U.starProjection x ∈ closure R := hdense (U.starProjection_apply_mem x)
  obtain ⟨t, ht, hdist⟩ := Metric.mem_closure_iff.mp hp ε hε
  refine ⟨clip t, hclipR t ht, hQ t ht, ?_⟩
  exact (projection_clipping_distance_le U x t (clip t) (hR ht) (hR (hclipR t ht))
    (hcontract t ht)).trans_lt (by simpa only [dist_eq_norm] using hdist)

end Hindman168
