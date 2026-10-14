import Hindman168.NativeLieSubalgebraSmoothRetraction

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

/-! Smoothness is proved for the existing subgroup multiplication and
inverse, using the smooth inclusion and its constructed smooth retraction. -/

theorem nativeLieSubalgebra_mul_contMDiff (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    let J := 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S)
    ContMDiff (J.prod J) J ∞ (fun p : nativeLieSubalgebraSubgroup (E := E) S ×
      nativeLieSubalgebraSubgroup (E := E) S => p.1 * p.2) := by
  letI := nativeLieSubalgebraChartedSpace (E := E) S
  let J := 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S)
  let K := nativeLieSubalgebraSubgroup (E := E) S
  have h1 : ContMDiff (J.prod J) I ∞ (fun p : K × K => p.1.val) :=
    (nativeLieSubalgebra_inclusion_contMDiff S).comp contMDiff_fst
  have h2 : ContMDiff (J.prod J) I ∞ (fun p : K × K => p.2.val) :=
    (nativeLieSubalgebra_inclusion_contMDiff S).comp contMDiff_snd
  have h := (nativeLieSubalgebraRetraction_contMDiff S).comp (h1.mul h2)
  exact h.congr (fun p => (nativeLieSubalgebraRetraction_left S (p.1 * p.2)).symm)

theorem nativeLieSubalgebra_inv_contMDiff (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    let J := 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S)
    ContMDiff J J ∞ (fun g : nativeLieSubalgebraSubgroup (E := E) S => g⁻¹) := by
  letI := nativeLieSubalgebraChartedSpace (E := E) S
  have h := (nativeLieSubalgebraRetraction_contMDiff S).comp
    (nativeLieSubalgebra_inclusion_contMDiff S).inv
  exact h.congr (fun g => (nativeLieSubalgebraRetraction_left S g⁻¹).symm)

theorem nativeLieSubalgebra_lieGroup (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    LieGroup 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S) ∞ (nativeLieSubalgebraSubgroup (E := E) S) := by
  letI := nativeLieSubalgebraChartedSpace (E := E) S
  letI := nativeLieSubalgebra_isManifold S
  exact { contMDiff_mul := nativeLieSubalgebra_mul_contMDiff S
          contMDiff_inv := nativeLieSubalgebra_inv_contMDiff S }

theorem nativeLieSubalgebra_boundaryless (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    BoundarylessManifold 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S)
      (nativeLieSubalgebraSubgroup (E := E) S) := by
  letI := nativeLieSubalgebraChartedSpace (E := E) S
  infer_instance

end Hindman168

