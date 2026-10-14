import Hindman168.LieInvariantParameterField
import Hindman168.LieOneParameterVelocity

/-! The original native invariant field in the identity chart, with
its tangent parameter kept as a genuine normed coordinate. -/

namespace Hindman168
open Bundle Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G] [BoundarylessManifold I G]

 noncomputable def lieInvariantCoordinateField (q : E × E) : E :=
  tangentCoordChange I ((extChartAt I (1 : G)).symm q.2) (1 : G)
    ((extChartAt I (1 : G)).symm q.2)
    (mulInvariantVectorField (I := I) q.1 ((extChartAt I (1 : G)).symm q.2))

 theorem lieInvariantCoordinateField_contDiffAt :
    ContDiffAt ℝ 1 (lieInvariantCoordinateField (I := I) (G := G))
      (0, extChartAt I (1 : G) (1 : G)) := by
  have h : ContMDiffAt (𝓘(ℝ, E).prod I) I.tangent 1
      (fun p : E × G => (⟨p.2, mulInvariantVectorField (I := I) p.1 p.2⟩ :
        TangentBundle I G)) (0, (1 : G)) := lie_invariant_field_joint_contMDiff_one.contMDiffAt
  rw [contMDiffAt_iff] at h
  have hc := h.2.contDiffAt (range_mem_nhds_isInteriorPoint
    (BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ, E).prod I) (x := (0, (1 : G)))))
  convert! hc.snd using 1

 omit [BoundarylessManifold I G] in
 theorem lieInvariantCoordinateField_zero_parameter (z : E) :
    lieInvariantCoordinateField (I := I) (G := G) (0, z) = 0 := by
  unfold lieInvariantCoordinateField
  have hz : (mulInvariantVectorField (I := I) (0 : E)
      ((extChartAt I (1 : G)).symm z) : E) = 0 := by
    change (mfderiv I I (fun x : G => ((extChartAt I (1 : G)).symm z) * x) (1 : G) :
      E →L[ℝ] E) 0 = 0
    exact map_zero _
  rw [hz]
  exact map_zero _

 omit [BoundarylessManifold I G] in
 theorem lieInvariantCoordinateField_identity_coordinate (v : E) :
    lieInvariantCoordinateField (I := I) (G := G)
      (v, extChartAt I (1 : G) (1 : G)) = v := by
  unfold lieInvariantCoordinateField
  rw [(extChartAt I (1 : G)).left_inv (mem_extChartAt_source (I := I) (1 : G))]
  erw [lie_invariant_field_one]
  exact tangentCoordChange_self (mem_extChartAt_source (I := I) (1 : G))

 theorem lieInvariantCoordinateField_hasFDerivAt :
    HasFDerivAt (lieInvariantCoordinateField (I := I) (G := G))
      (ContinuousLinearMap.fst ℝ E E) (0, extChartAt I (1 : G) (1 : G)) := by
  let z₀ := extChartAt I (1 : G) (1 : G)
  have h := (lieInvariantCoordinateField_contDiffAt (I := I) (G := G)).differentiableAt
    (by norm_num : (1 : ℕ∞ω) ≠ 0) |>.hasFDerivAt
  have hv := h.comp (0 : E) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : E) z₀)
  have hz := h.comp z₀ (hasFDerivAt_prodMk_right (𝕜 := ℝ) (0 : E) z₀)
  have heqv : (fun v : E => lieInvariantCoordinateField (I := I) (G := G) (v, z₀)) = id :=
    funext (lieInvariantCoordinateField_identity_coordinate (I := I) (G := G))
  have heqz : (fun z : E => lieInvariantCoordinateField (I := I) (G := G) (0, z)) =
      (fun _ : E => (0 : E)) :=
    funext (lieInvariantCoordinateField_zero_parameter (I := I) (G := G))
  simp only [Function.comp_def] at hv hz
  rw [heqv] at hv
  rw [heqz] at hz
  have hdv := hv.unique (hasFDerivAt_id (𝕜 := ℝ) (0 : E))
  have hdz := hz.unique (hasFDerivAt_const (𝕜 := ℝ) (0 : E) z₀)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro q
  have h₁ := congrArg (fun D : E →L[ℝ] E => D q.1) hdv
  have h₂ := congrArg (fun D : E →L[ℝ] E => D q.2) hdz
  change (fderiv ℝ (lieInvariantCoordinateField (I := I) (G := G)) (0, z₀)) (q.1, 0) = q.1 at h₁
  change (fderiv ℝ (lieInvariantCoordinateField (I := I) (G := G)) (0, z₀)) (0, q.2) = 0 at h₂
  have heq : q = (q.1, 0) + (0, q.2) := by ext <;> simp
  change (fderiv ℝ (lieInvariantCoordinateField (I := I) (G := G)) (0, z₀)) q = q.1
  calc
    (fderiv ℝ (lieInvariantCoordinateField (I := I) (G := G)) (0, z₀)) q =
        (fderiv ℝ (lieInvariantCoordinateField (I := I) (G := G)) (0, z₀)) (q.1, 0) +
        (fderiv ℝ (lieInvariantCoordinateField (I := I) (G := G)) (0, z₀)) (0, q.2) := by
      rw [← map_add, ← heq]
    _ = q.1 := by rw [h₁, h₂, add_zero]

 theorem lieInvariantCoordinateField_hasStrictFDerivAt :
    HasStrictFDerivAt (lieInvariantCoordinateField (I := I) (G := G))
      (ContinuousLinearMap.fst ℝ E E) (0, extChartAt I (1 : G) (1 : G)) := by
  have h := (lieInvariantCoordinateField_contDiffAt (I := I) (G := G)).hasStrictFDerivAt
    (by norm_num : (1 : ℕ∞ω) ≠ 0)
  rw [(lieInvariantCoordinateField_hasFDerivAt (I := I) (G := G)).fderiv] at h
  exact h

 noncomputable def lieFrozenCoordinateField (q : E × E) : E × E :=
  (0, lieInvariantCoordinateField (I := I) (G := G) q)

 noncomputable def lieFrozenCoordinateLinearization : (E × E) →L[ℝ] (E × E) :=
  (0 : (E × E) →L[ℝ] E).prod (ContinuousLinearMap.fst ℝ E E)

 theorem lieFrozenCoordinateField_hasStrictFDerivAt :
    HasStrictFDerivAt (lieFrozenCoordinateField (I := I) (G := G))
      (lieFrozenCoordinateLinearization (E := E)) (0, extChartAt I (1 : G) (1 : G)) := by
  exact (hasStrictFDerivAt_const (0 : E) (0, extChartAt I (1 : G) (1 : G))).prodMk
    (lieInvariantCoordinateField_hasStrictFDerivAt (I := I) (G := G))

 omit [BoundarylessManifold I G] in
 theorem lieFrozenCoordinateLinearization_square_zero :
    (lieFrozenCoordinateLinearization (E := E)).comp
      (lieFrozenCoordinateLinearization (E := E)) = 0 := by
  ext q <;> rfl

 omit [BoundarylessManifold I G] in
 theorem lieFrozenCoordinateField_equilibrium :
    lieFrozenCoordinateField (I := I) (G := G) (0, extChartAt I (1 : G) (1 : G)) = 0 := by
  simp [lieFrozenCoordinateField, lieInvariantCoordinateField_zero_parameter]

end Hindman168
