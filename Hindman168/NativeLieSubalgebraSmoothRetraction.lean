import Hindman168.NativeLieSubalgebraCharted
import Hindman168.FiniteRealSubmoduleRetraction

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeLieSubalgebra_inclusion_contMDiff
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    ContMDiff 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S) I ∞
      ((↑) : nativeLieSubalgebraSubgroup (E := E) S → G) := by
  letI := nativeLieSubalgebraChartedSpace (E := E) S
  let V := nativeLieSubalgebraModel (E := E) S
  let e := nativeLieSubalgebraExponentialDiffeomorph (E := E) S
  have hi : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ V.subtype :=
    V.subtype.toContinuousLinearMap.contDiff.contMDiff
  have h := (nativeLieExponential_contMDiff (E := E) (I := I) (G := G)).comp
    (hi.comp e.contMDiff_invFun)
  apply h.congr
  intro g
  exact (nativeLieExponential_globalLogarithm (E := E) (I := I) (G := G) g.val).symm

noncomputable def nativeLieSubalgebraRetraction
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (g : G) : nativeLieSubalgebraSubgroup (E := E) S :=
  nativeLieSubalgebraExponentialHomeomorph (E := E) S
    (finiteRealSubmoduleRetraction (nativeLieSubalgebraModel (E := E) S)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g))

theorem nativeLieSubalgebraRetraction_left
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (g : nativeLieSubalgebraSubgroup (E := E) S) :
    nativeLieSubalgebraRetraction (E := E) S g.val = g := by
  let e := nativeLieSubalgebraExponentialHomeomorph (E := E) S
  have h := finiteRealSubmoduleRetraction_left (nativeLieSubalgebraModel (E := E) S) (e.symm g)
  exact (congrArg e h).trans (e.apply_symm_apply g)

theorem nativeLieSubalgebraRetraction_contMDiff
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    ContMDiff I 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S) ∞
      (nativeLieSubalgebraRetraction (E := E) S : G → nativeLieSubalgebraSubgroup (E := E) S) := by
  letI := nativeLieSubalgebraChartedSpace (E := E) S
  let e := nativeLieSubalgebraExponentialDiffeomorph (E := E) S
  let p := finiteRealSubmoduleRetraction (nativeLieSubalgebraModel (E := E) S)
  exact e.contMDiff_toFun.comp (p.contDiff.contMDiff.comp
    (nativeLieGlobalLogarithm_contMDiff (E := E) (I := I) (G := G)))

end Hindman168

