import Hindman168.NativeLieLogarithmVectorField
import Hindman168.ClosedSubmoduleIntervalIntegral

/-! Any actual Lie subalgebra of the original native Lie algebra is
preserved by the original adjoint generator at its internal parameters,
and hence by the genuine finite inverse differential. No matrix model,
subgroup closure or assumed BCH is used. -/

namespace Hindman168
open Function Set Finset
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieSubalgebraModel
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) : Submodule ℝ E := S.toSubmodule

omit [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieSubalgebraModel_closed [FiniteDimensional ℝ E]
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    IsClosed (nativeLieSubalgebraModel (E := E) S : Set E) :=
  (nativeLieSubalgebraModel (E := E) S).closed_of_finiteDimensional

 theorem nativeLieAdjointGenerator_mem_subalgebra
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) {v w : E}
    (hv : v ∈ nativeLieSubalgebraModel S) (hw : w ∈ nativeLieSubalgebraModel S) :
    nativeLieAdjointGenerator (I := I) (G := G) v w ∈ nativeLieSubalgebraModel S := by
  let x : GroupLieAlgebra I G := v
  let y : GroupLieAlgebra I G := w
  have h : ⁅x, y⁆ ∈ S := S.lie_mem hv hw
  exact (nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) x y).symm ▸ h

 theorem nativeLieAdjointGenerator_pow_mem_subalgebra
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) {v w : E}
    (hv : v ∈ nativeLieSubalgebraModel S) (hw : w ∈ nativeLieSubalgebraModel S) (n : ℕ) :
    (nativeLieAdjointGenerator (I := I) (G := G) v ^ n) w ∈ nativeLieSubalgebraModel S := by
  let B : E →L[ℝ] E := nativeLieAdjointGenerator (I := I) (G := G) v
  change (B ^ n) w ∈ nativeLieSubalgebraModel S
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self] using hw
  | succ n ih =>
    rw [pow_succ']
    exact nativeLieAdjointGenerator_mem_subalgebra S hv ih

variable [Group.IsNilpotent G]

 theorem nativeLieDexpDefect_mem_subalgebra
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) {v w : E}
    (hv : v ∈ nativeLieSubalgebraModel S) (hw : w ∈ nativeLieSubalgebraModel S) :
    nativeLieDexpDefect (I := I) (G := G) v w ∈ nativeLieSubalgebraModel S := by
  rw [nativeLieDexpDefect_finite_formula]
  simp only [neg_apply, _root_.sum_apply, smul_apply]
  apply (nativeLieSubalgebraModel S).neg_mem
  apply Submodule.sum_mem
  intro n _
  exact Submodule.smul_mem _ _ (nativeLieAdjointGenerator_pow_mem_subalgebra S hv hw (n + 1))

 theorem nativeLieDexpDefect_pow_mem_subalgebra
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) {v w : E}
    (hv : v ∈ nativeLieSubalgebraModel S) (hw : w ∈ nativeLieSubalgebraModel S) (n : ℕ) :
    (nativeLieDexpDefect (I := I) (G := G) v ^ n) w ∈ nativeLieSubalgebraModel S := by
  let W : E →L[ℝ] E := nativeLieDexpDefect (I := I) (G := G) v
  change (W ^ n) w ∈ nativeLieSubalgebraModel S
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self] using hw
  | succ n ih =>
    rw [pow_succ']
    exact nativeLieDexpDefect_mem_subalgebra S hv ih

 theorem nativeLieDexpFiniteInverse_mem_subalgebra
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) {v w : E}
    (hv : v ∈ nativeLieSubalgebraModel S) (hw : w ∈ nativeLieSubalgebraModel S) :
    nativeLieDexpFiniteInverse (I := I) (G := G) v w ∈ nativeLieSubalgebraModel S := by
  unfold nativeLieDexpFiniteInverse
  rw [_root_.sum_apply]
  apply Submodule.sum_mem
  intro n _
  exact nativeLieDexpDefect_pow_mem_subalgebra S hv hw n

 theorem nativeLieLogarithmVectorField_mem_subalgebra
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) {v w : E}
    (hv : v ∈ nativeLieSubalgebraModel S) (hw : w ∈ nativeLieSubalgebraModel S) :
    nativeLieLogarithmVectorField (I := I) (G := G) w v ∈ nativeLieSubalgebraModel S :=
  nativeLieDexpFiniteInverse_mem_subalgebra S hv hw

end Hindman168
