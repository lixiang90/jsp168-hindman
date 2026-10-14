import Hindman168.DiscreteCosetProductSmooth
import Hindman168.NativeDiscreteCosetManifold
import Hindman168.NativeLieSubalgebraLieGroup
import Hindman168.RoughConjugateOrbitMap
import Hindman168.RoughNativeConjugateLatticeCompact

/-! Smoothness of the actual induced orbit map, including the left
factor as a joint parameter, on the genuine discrete coset manifolds. -/
namespace Hindman168
open Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_conjugate_orbit_joint_contMDiff (Γ : Subgroup G)
    [DiscreteTopology Γ] (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (g : G) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    letI := nativeLieSubalgebra_lieGroup S
    letI := rough_native_conjugate_lattice_intersection_discrete Γ g S
    letI := nativeDiscreteCosetChartedSpace (E := E) (I := I) Γ
    let Δ := (roughConjugateSubgroup Γ g).comap (nativeLieSubalgebraSubgroup (E := E) S).subtype
    letI : IsTopologicalGroup (nativeLieSubalgebraSubgroup (E := E) S) :=
      topologicalGroup_of_lieGroup 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S) ∞
    letI := discreteCosetGlobalChartedSpace (nativeLieSubalgebraExponentialDiffeomorph (E := E) S) Δ
    ContMDiff (I.prod 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S)) 𝓘(ℝ, E) ∞
      (fun p : G × (nativeLieSubalgebraSubgroup (E := E) S ⧸ Δ) =>
        roughConjugateOrbitMap Γ (nativeLieSubalgebraSubgroup (E := E) S) g p.1 p.2) := by
  letI := nativeLieSubalgebraChartedSpace (E := E) S
  letI := nativeLieSubalgebra_lieGroup S
  letI := rough_native_conjugate_lattice_intersection_discrete Γ g S
  letI := nativeDiscreteCosetChartedSpace (E := E) (I := I) Γ
  let L := nativeLieSubalgebraSubgroup (E := E) S
  let J := 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S)
  let Δ := (roughConjugateSubgroup Γ g).comap L.subtype
  letI : IsTopologicalGroup L := topologicalGroup_of_lieGroup J ∞
  apply discreteCoset_product_contMDiff_of_projection
    (nativeLieSubalgebraExponentialDiffeomorph (E := E) S) Δ
  have hi : ContMDiff (I.prod J) I ∞ (fun p : G × L => p.2.val) :=
    (nativeLieSubalgebra_inclusion_contMDiff S).comp contMDiff_snd
  have hm : ContMDiff (I.prod J) I ∞ (fun p : G × L => p.1 * p.2.val * g) :=
    (contMDiff_fst.mul hi).mul contMDiff_const
  exact (nativeDiscreteCoset_projection_contMDiff (E := E) (I := I) Γ).comp hm

end Hindman168
