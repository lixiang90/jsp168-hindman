import Hindman168.NativeLieSubalgebraModel
import Hindman168.NativeLieExponentialProductLog

/-! Actual finite Picard product logarithms stay in any original native
Lie subalgebra. Actual finite-dimensional closure and actual interval
integral membership justify every step, without assumed subgroup closure. -/

namespace Hindman168
open Function Set MeasureTheory
open scoped Interval Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieSubalgebraPicard_mem
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) {u w : E}
    (hu : u ∈ nativeLieSubalgebraModel S) (hw : w ∈ nativeLieSubalgebraModel S)
    (n : ℕ) (t : ℝ) :
    continuousPicardIterate (nativeLieLogarithmVectorField (I := I) (G := G) w) u n t ∈
      nativeLieSubalgebraModel S := by
  let F : E → E := nativeLieLogarithmVectorField (I := I) (G := G) w
  have hF : Continuous F := (nativeLieLogarithmVectorField_contDiff w).continuous
  change continuousPicardIterate F u n t ∈ nativeLieSubalgebraModel S
  induction n generalizing t with
  | zero => exact hu
  | succ n ih =>
    apply (nativeLieSubalgebraModel S).add_mem hu
    apply closedSubmodule_intervalIntegral_mem _ (nativeLieSubalgebraModel_closed S)
      ((hF.comp (continuousPicardIterate_continuous hF u n)).intervalIntegrable 0 t)
    intro s
    exact nativeLieLogarithmVectorField_mem_subalgebra S (ih s) hw

 theorem nativeLieLogarithmLift_mem_subalgebra
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) {u w : E}
    (hu : u ∈ nativeLieSubalgebraModel S) (hw : w ∈ nativeLieSubalgebraModel S) (t : ℝ) :
    nativeLieLogarithmLift (E := E) (I := I) (G := G) w u t ∈ nativeLieSubalgebraModel S :=
  nativeLieSubalgebraPicard_mem S hu hw _ t

end Hindman168
