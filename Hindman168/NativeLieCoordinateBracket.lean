import Hindman168.NativeLieAdjointGenerator
import Hindman168.NativeLieRightTranslation

/-! The original native Lie bracket in the genuine identity chart. The
coordinate vector fields are the actual inverse-chart pullbacks, and their
regularity comes from actual native invariant-field regularity. -/

namespace Hindman168
open Bundle Function Set Filter Topology VectorField
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieCoordinateVectorField (v : E) : E → E :=
  mpullbackWithin 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm
    (mulInvariantVectorField (I := I) (G := G) v) (range I)

omit [CompleteSpace E] [LieGroup I ∞ G] in
 theorem nativeLieIdentityChart_range_nhds :
    range I ∈ 𝓝 (extChartAt I (1 : G) (1 : G)) :=
  range_mem_nhds_isInteriorPoint (BoundarylessManifold.isInteriorPoint (I := I) (x := (1 : G)))

omit [CompleteSpace E] [LieGroup I ∞ G] in
 theorem nativeLieIdentityChart_target_nhds :
    (extChartAt I (1 : G)).target ∈ 𝓝 (extChartAt I (1 : G) (1 : G)) := by
  have h := extChartAt_target_mem_nhdsWithin (I := I) (1 : G)
  rw [nhdsWithin_eq_nhds.mpr (nativeLieIdentityChart_range_nhds (I := I) (G := G))] at h
  exact h

omit [CompleteSpace E] [BoundarylessManifold I G] in
 theorem nativeLieCoordinateVectorField_identity (v : E) :
    nativeLieCoordinateVectorField (I := I) (G := G) v
      (extChartAt I (1 : G) (1 : G)) = v := by
  unfold nativeLieCoordinateVectorField
  rw [mpullbackWithin_apply]
  rw [(extChartAt I (1 : G)).left_inv (mem_extChartAt_source (I := I) (1 : G))]
  erw [lie_invariant_field_one]
  exact mfderivWithin_extChartAt_symm_inverse_apply v

omit [CompleteSpace E] [BoundarylessManifold I G] in
 theorem nativeLieCoordinateVectorField_eq_chart_derivative (v : E) {z : E}
    (hz : z ∈ (extChartAt I (1 : G)).target) :
    nativeLieCoordinateVectorField (I := I) (G := G) v z =
      mfderiv I 𝓘(ℝ, E) (extChartAt I (1 : G)) ((extChartAt I (1 : G)).symm z)
        (mulInvariantVectorField (I := I) (G := G) v ((extChartAt I (1 : G)).symm z)) := by
  unfold nativeLieCoordinateVectorField
  rw [mpullbackWithin_apply]
  have hi := ContinuousLinearMap.inverse_eq
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hz)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hz)
  rw [hi]
  rfl

omit [CompleteSpace E] [BoundarylessManifold I G] in
 theorem nativeLieInvariantVectorField_contMDiff_smooth (v : E) :
    ContMDiff I I.tangent ∞ (fun g : G =>
      (⟨g, mulInvariantVectorField (I := I) (G := G) v g⟩ : TangentBundle I G)) := by
  have h := (lie_invariant_field_joint_contMDiff_smooth (I := I) (G := G)).comp
    ((contMDiff_const : ContMDiff I 𝓘(ℝ, E) ∞ (fun _ : G => v)).prodMk contMDiff_id)
  exact h

 theorem nativeLieCoordinateVectorField_contDiffAt_identity (v : E) :
    ContDiffAt ℝ ∞ (nativeLieCoordinateVectorField (I := I) (G := G) v)
      (extChartAt I (1 : G) (1 : G)) := by
  have h := contMDiffWithinAt_mpullbackWithin_extChartAt_symm
    (I := I) (x := (1 : G)) (s := univ) (m := ∞) (n := ∞)
    (nativeLieInvariantVectorField_contMDiff_smooth (I := I) (G := G) v).contMDiffAt.contMDiffWithinAt
    uniqueMDiffOn_univ (mem_univ _) (by rw [ENat.coe_top_add_one])
  simp only [preimage_univ, inter_univ] at h
  have hn := h.contMDiffAt (nativeLieIdentityChart_target_nhds (I := I) (G := G))
  have hs := (contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).contMDiffAt.comp
    (extChartAt I (1 : G) (1 : G)) hn
  convert! hs.contDiffAt using 1

omit [CompleteSpace E] in
 theorem nativeLieBracket_eq_coordinate_bracket (v w : GroupLieAlgebra I G) :
    (⁅v, w⁆ : GroupLieAlgebra I G) =
      lieBracket ℝ (nativeLieCoordinateVectorField (I := I) (G := G) v)
        (nativeLieCoordinateVectorField (I := I) (G := G) w)
        (extChartAt I (1 : G) (1 : G)) := by
  rw [GroupLieAlgebra.bracket_def, mlieBracket, mlieBracketWithin_apply]
  erw [mfderiv_extChartAt_self, ContinuousLinearMap.inverse_id]
  simp only [preimage_univ, univ_inter]
  rw [lieBracketWithin_of_mem_nhds (nativeLieIdentityChart_range_nhds (I := I) (G := G))]
  rfl

omit [CompleteSpace E] in
 theorem nativeLieBracket_eq_coordinate_derivatives (v w : GroupLieAlgebra I G) :
    (⁅v, w⁆ : GroupLieAlgebra I G) =
      fderiv ℝ (nativeLieCoordinateVectorField (I := I) (G := G) w)
          (extChartAt I (1 : G) (1 : G)) v -
        fderiv ℝ (nativeLieCoordinateVectorField (I := I) (G := G) v)
          (extChartAt I (1 : G) (1 : G)) w := by
  rw [nativeLieBracket_eq_coordinate_bracket]
  unfold lieBracket
  rw [nativeLieCoordinateVectorField_identity, nativeLieCoordinateVectorField_identity]

end Hindman168
