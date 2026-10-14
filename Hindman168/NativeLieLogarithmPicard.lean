import Hindman168.ContinuousPicardIteration
import Hindman168.NativeLieLogarithmVectorField
import Hindman168.ClosedSubmoduleIntervalIntegral

/-! A genuine finite Picard construction in the original Lie algebra.
Actual iterated integrals gain one original lower-central layer per step.
The actual original group nilpotency class kills the next increment, so
the constructed global curve satisfies the actual logarithm lifting ODE. -/

namespace Hindman168
open Function Set MeasureTheory
open scoped Interval Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieLogarithmPicard_increment (w u : E) (n : ℕ) (t : ℝ) :
    continuousPicardIterate (nativeLieLogarithmVectorField (I := I) (G := G) w) u (n + 1) t -
      continuousPicardIterate (nativeLieLogarithmVectorField (I := I) (G := G) w) u n t ∈
        nativeLieLowerCentralModel (I := I) (G := G) n := by
  let F : E → E := nativeLieLogarithmVectorField (I := I) (G := G) w
  have hF : Continuous F := (nativeLieLogarithmVectorField_contDiff w).continuous
  change continuousPicardIterate F u (n + 1) t - continuousPicardIterate F u n t ∈ _
  induction n generalizing t with
  | zero =>
    rw [nativeLieLowerCentralModel_zero]
    exact Submodule.mem_top
  | succ n ih =>
    rw [continuousPicardIterate_succ_sub_succ hF]
    apply nativeLieLowerCentralModel_intervalIntegral_mem
      (((hF.comp (continuousPicardIterate_continuous hF u (n + 1))).sub
        (hF.comp (continuousPicardIterate_continuous hF u n))).intervalIntegrable 0 t)
    intro s
    exact nativeLieLogarithmVectorField_sub_mem_lowerCentral_next w (ih s)

 theorem nativeLieLogarithmPicard_stabilizes (w u : E) :
    continuousPicardIterate (nativeLieLogarithmVectorField (I := I) (G := G) w) u
        (Group.nilpotencyClass G + 1) =
      continuousPicardIterate (nativeLieLogarithmVectorField (I := I) (G := G) w) u
        (Group.nilpotencyClass G) := by
  funext t
  have h := nativeLieLogarithmPicard_increment (I := I) (G := G) w u
    (Group.nilpotencyClass G) t
  rw [nativeLieLowerCentralModel_nilpotencyClass_bot, Submodule.mem_bot] at h
  exact sub_eq_zero.mp h

noncomputable def nativeLieLogarithmLift (w u : E) : ℝ → E :=
  continuousPicardIterate (nativeLieLogarithmVectorField (I := I) (G := G) w) u
    (Group.nilpotencyClass G + 1)

omit [Group.IsNilpotent G] [FiniteDimensional ℝ E] in
 theorem nativeLieLogarithmLift_zero (w u : E) :
    nativeLieLogarithmLift (I := I) (G := G) w u 0 = u :=
  continuousPicardIterate_zero _ _ _

omit [FiniteDimensional ℝ E] in
 theorem nativeLieLogarithmLift_continuous (w u : E) :
    Continuous (nativeLieLogarithmLift (I := I) (G := G) w u) :=
  continuousPicardIterate_continuous (nativeLieLogarithmVectorField_contDiff w).continuous u _

 theorem nativeLieLogarithmLift_hasDerivAt (w u : E) (t : ℝ) :
    HasDerivAt (nativeLieLogarithmLift (I := I) (G := G) w u)
      (nativeLieLogarithmVectorField (I := I) (G := G) w
        (nativeLieLogarithmLift (I := I) (G := G) w u t)) t := by
  have h := continuousPicardIterate_succ_hasDerivAt
    (nativeLieLogarithmVectorField_contDiff (I := I) (G := G) w).continuous u
    (Group.nilpotencyClass G) t
  have he := nativeLieLogarithmPicard_stabilizes (I := I) (G := G) w u
  change HasDerivAt (nativeLieLogarithmLift (I := I) (G := G) w u) _ t at h
  rw [← he] at h
  exact h

end Hindman168
