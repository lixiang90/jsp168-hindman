import Hindman168.NativeLieDexpDefectFiltration
import Hindman168.OperatorPowerFiltrationDifference

/-! The genuine finite inverse of original native dexp preserves the
actual native lower central series. If its original parameter changes
within layer j, its value on every vector changes within layer j+1.
All identities follow from actual native operators and their proved
finite series; no inverse filtration property is supplied. -/

namespace Hindman168
open Function Set Topology Finset
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieDexp_inverse_eq_finiteInverse (v : E) :
    (nativeLieDexp (I := I) (G := G) v).inverse =
      nativeLieDexpFiniteInverse (I := I) (G := G) v :=
  ContinuousLinearMap.inverse_eq (nativeLieDexp_mul_finiteInverse v)
    (nativeLieDexp_finiteInverse_mul v)

 theorem nativeLieDexpFiniteInverse_mem_lowerCentral (v : E) {u : E} {j : ℕ}
    (hu : u ∈ nativeLieLowerCentralModel (I := I) (G := G) j) :
    nativeLieDexpFiniteInverse (I := I) (G := G) v u ∈
      nativeLieLowerCentralModel (I := I) (G := G) j := by
  unfold nativeLieDexpFiniteInverse
  rw [_root_.sum_apply]
  apply Submodule.sum_mem
  intro n _
  exact nativeLieLowerCentralModel_antitone (I := I) (G := G) (Nat.le_add_right j n)
    (nativeLieDexpDefect_pow_mem_lowerCentral v hu n)

omit [Group.IsNilpotent G] in
 theorem nativeLieAdjointGenerator_pow_action_sub_mem_lowerCentral_next {v w : E} {j : ℕ}
    (h : v - w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) (n : ℕ) (u : E) :
    (nativeLieAdjointGenerator (I := I) (G := G) v ^ n) u -
      (nativeLieAdjointGenerator (I := I) (G := G) w ^ n) u ∈
        nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
  apply operator_pow_sub_mem_submodule
  · intro x hx
    exact nativeLieLowerCentralModel_antitone (I := I) (G := G) (Nat.le_succ (j + 1))
      (nativeLieAdjointGenerator_mem_lowerCentral_next v hx)
  · exact nativeLieAdjointGenerator_action_sub_mem_lowerCentral_next h

 theorem nativeLieDexp_action_sub_mem_lowerCentral_next {v w : E} {j : ℕ}
    (h : v - w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) (u : E) :
    nativeLieDexp (I := I) (G := G) v u - nativeLieDexp (I := I) (G := G) w u ∈
      nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
  rw [nativeLieDexp_finite_formula, nativeLieDexp_finite_formula]
  simp only [_root_.sum_apply, smul_apply]
  rw [← sum_sub_distrib]
  apply Submodule.sum_mem
  intro n _
  rw [← smul_sub]
  exact Submodule.smul_mem _ _ (nativeLieAdjointGenerator_pow_action_sub_mem_lowerCentral_next h n u)

 theorem nativeLieDexpDefect_action_sub_mem_lowerCentral_next {v w : E} {j : ℕ}
    (h : v - w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) (u : E) :
    nativeLieDexpDefect (I := I) (G := G) v u -
      nativeLieDexpDefect (I := I) (G := G) w u ∈
        nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
  have he : nativeLieDexpDefect (I := I) (G := G) v u -
      nativeLieDexpDefect (I := I) (G := G) w u =
        -(nativeLieDexp (I := I) (G := G) v u - nativeLieDexp (I := I) (G := G) w u) := by
    simp only [nativeLieDexpDefect, sub_apply, one_apply_eq_self]
    abel
  rw [he]
  exact Submodule.neg_mem _ (nativeLieDexp_action_sub_mem_lowerCentral_next h u)

 theorem nativeLieDexpDefect_pow_action_sub_mem_lowerCentral_next {v w : E} {j : ℕ}
    (h : v - w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) (n : ℕ) (u : E) :
    (nativeLieDexpDefect (I := I) (G := G) v ^ n) u -
      (nativeLieDexpDefect (I := I) (G := G) w ^ n) u ∈
        nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
  apply operator_pow_sub_mem_submodule
  · intro x hx
    exact nativeLieLowerCentralModel_antitone (I := I) (G := G) (Nat.le_succ (j + 1))
      (nativeLieDexpDefect_mem_lowerCentral_next v hx)
  · exact nativeLieDexpDefect_action_sub_mem_lowerCentral_next h

 theorem nativeLieDexpFiniteInverse_action_sub_mem_lowerCentral_next {v w : E} {j : ℕ}
    (h : v - w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) (u : E) :
    nativeLieDexpFiniteInverse (I := I) (G := G) v u -
      nativeLieDexpFiniteInverse (I := I) (G := G) w u ∈
        nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
  unfold nativeLieDexpFiniteInverse
  rw [_root_.sum_apply, _root_.sum_apply, ← sum_sub_distrib]
  apply Submodule.sum_mem
  intro n _
  exact nativeLieDexpDefect_pow_action_sub_mem_lowerCentral_next h n u

end Hindman168
