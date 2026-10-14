import Hindman168.NativeLieSubalgebraSubgroup

/-! The actual exponential image of any original native Lie ideal is
normal in the original connected nilpotent group. The actual finite
adjoint formula and genuine whole-group exponential surjectivity prove
ideal invariance under every actual original group conjugation. -/

namespace Hindman168
open Function Set Finset
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieAdjointGenerator_mem_ideal
    (J : LieIdeal ℝ (GroupLieAlgebra I G)) (v : E) {w : E}
    (hw : w ∈ nativeLieSubalgebraModel (E := E) J.toLieSubalgebra) :
    nativeLieAdjointGenerator (I := I) (G := G) v w ∈
      nativeLieSubalgebraModel (E := E) J.toLieSubalgebra := by
  let x : GroupLieAlgebra I G := v
  let y : GroupLieAlgebra I G := w
  have h : ⁅x, y⁆ ∈ J := J.lie_mem hw
  exact (nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) x y).symm ▸ h

 theorem nativeLieAdjointGenerator_pow_mem_ideal
    (J : LieIdeal ℝ (GroupLieAlgebra I G)) (v : E) {w : E}
    (hw : w ∈ nativeLieSubalgebraModel (E := E) J.toLieSubalgebra) (n : ℕ) :
    (nativeLieAdjointGenerator (I := I) (G := G) v ^ n) w ∈
      nativeLieSubalgebraModel (E := E) J.toLieSubalgebra := by
  let B : E →L[ℝ] E := nativeLieAdjointGenerator (I := I) (G := G) v
  change (B ^ n) w ∈ nativeLieSubalgebraModel (E := E) J.toLieSubalgebra
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self] using hw
  | succ n ih =>
    rw [pow_succ']
    exact nativeLieAdjointGenerator_mem_ideal J v ih

variable [Group.IsNilpotent G]

 theorem nativeLieAdjoint_exponential_mem_ideal
    (J : LieIdeal ℝ (GroupLieAlgebra I G)) (v : E) {w : E}
    (hw : w ∈ nativeLieSubalgebraModel (E := E) J.toLieSubalgebra) :
    (nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) : E →L[ℝ] E) w ∈
      nativeLieSubalgebraModel (E := E) J.toLieSubalgebra := by
  let A : E →L[ℝ] E := nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v)
  have he : A = ∑ n ∈ range (Group.nilpotencyClass G),
      (n.factorial : ℝ)⁻¹ • nativeLieAdjointGenerator (I := I) (G := G) v ^ n :=
    nativeLieAdjoint_exponential_finite_formula_of_group_isNilpotent v
  change A w ∈ nativeLieSubalgebraModel (E := E) J.toLieSubalgebra
  rw [he]
  simp only [_root_.sum_apply, smul_apply]
  apply Submodule.sum_mem
  intro n _
  exact Submodule.smul_mem _ _ (nativeLieAdjointGenerator_pow_mem_ideal J v hw n)

variable [FiniteDimensional ℝ E] [ConnectedSpace G]

 theorem nativeLieAdjoint_mem_ideal
    (J : LieIdeal ℝ (GroupLieAlgebra I G)) (g : G) {w : E}
    (hw : w ∈ nativeLieSubalgebraModel (E := E) J.toLieSubalgebra) :
    (nativeLieAdjoint (I := I) g : E →L[ℝ] E) w ∈
      nativeLieSubalgebraModel (E := E) J.toLieSubalgebra := by
  obtain ⟨v, rfl⟩ := nativeLieExponential_surjective (E := E) (I := I) (G := G) g
  exact nativeLieAdjoint_exponential_mem_ideal J v hw

 theorem nativeLieIdealSubgroup_normal
    (J : LieIdeal ℝ (GroupLieAlgebra I G)) :
    (nativeLieSubalgebraSubgroup (E := E) J.toLieSubalgebra).Normal := by
  refine ⟨?_⟩
  rintro a ⟨v, hv, rfl⟩ g
  let w : E := nativeLieAdjoint (I := I) g v
  exact ⟨w, nativeLieAdjoint_mem_ideal J g hv,
    (nativeLieAdjoint_exponential_conjugation (I := I) g v).symm⟩

end Hindman168
