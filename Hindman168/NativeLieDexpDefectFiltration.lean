import Hindman168.NativeLieLowerCentralModel
import Hindman168.NativeLieDexpInvertible
import Mathlib.Algebra.Ring.GeomSum

/-! The defect of the genuine original exponential differential lowers
the actual native lower central series by one. Its group-class power is
therefore zero, including class zero. This gives a true finite geometric
inverse for the actual original native dexp. -/

namespace Hindman168
open Function Set Topology Finset
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieDexpDefect (v : E) : E →L[ℝ] E :=
  1 - nativeLieDexp (I := I) (G := G) v

 theorem nativeLieDexpDefect_finite_formula (v : E) :
    nativeLieDexpDefect (I := I) (G := G) v =
      -(∑ n ∈ range (Group.nilpotencyClass G),
        ((-1 : ℝ) ^ (n + 1) / ((n + 2).factorial : ℝ)) •
          nativeLieAdjointGenerator (I := I) (G := G) v ^ (n + 1)) := by
  let c := Group.nilpotencyClass G
  let B : E →L[ℝ] E := nativeLieAdjointGenerator (I := I) (G := G) v
  let a : ℕ → ℝ := fun n => (-1 : ℝ) ^ n / ((n + 1).factorial : ℝ)
  have hp : B ^ c = 0 := nativeLieAdjointGenerator_pow_nilpotencyClass v
  have he : (∑ n ∈ range (c + 1), a n • B ^ n) = ∑ n ∈ range c, a n • B ^ n := by
    rw [sum_range_succ, hp, smul_zero, add_zero]
  have hD : nativeLieDexp (I := I) (G := G) v =
      (∑ n ∈ range c, a (n + 1) • B ^ (n + 1)) + 1 := by
    rw [nativeLieDexp_finite_formula, ← he, sum_range_succ']
    simp only [a, zero_add, pow_zero, Nat.factorial_one, Nat.cast_one, div_one, one_smul]
  unfold nativeLieDexpDefect
  rw [hD]
  change 1 - ((∑ n ∈ range c, a (n + 1) • B ^ (n + 1)) + 1) =
    -(∑ n ∈ range c, a (n + 1) • B ^ (n + 1))
  abel

 theorem nativeLieDexpDefect_mem_lowerCentral_next (v : E) {w : E} {j : ℕ}
    (hw : w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) :
    nativeLieDexpDefect (I := I) (G := G) v w ∈
      nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
  rw [nativeLieDexpDefect_finite_formula]
  simp only [neg_apply, _root_.sum_apply, smul_apply]
  apply (nativeLieLowerCentralModel (I := I) (G := G) (j + 1)).neg_mem
  apply Submodule.sum_mem
  intro n _
  apply Submodule.smul_mem
  exact nativeLieLowerCentralModel_antitone (I := I) (G := G) (by omega)
    (nativeLieAdjointGenerator_pow_mem_lowerCentral v hw (n + 1))

 theorem nativeLieDexpDefect_pow_mem_lowerCentral (v : E) {w : E} {j : ℕ}
    (hw : w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) (n : ℕ) :
    (nativeLieDexpDefect (I := I) (G := G) v ^ n) w ∈
      nativeLieLowerCentralModel (I := I) (G := G) (j + n) := by
  let W : E →L[ℝ] E := nativeLieDexpDefect (I := I) (G := G) v
  change (W ^ n) w ∈ nativeLieLowerCentralModel (I := I) (G := G) (j + n)
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self, Nat.add_zero] using hw
  | succ n ih =>
    rw [pow_succ']
    exact nativeLieDexpDefect_mem_lowerCentral_next (I := I) (G := G) v ih

 theorem nativeLieDexpDefect_pow_nilpotencyClass (v : E) :
    nativeLieDexpDefect (I := I) (G := G) v ^ Group.nilpotencyClass G = 0 := by
  apply ContinuousLinearMap.ext
  intro w
  have hw : w ∈ nativeLieLowerCentralModel (I := I) (G := G) 0 := by
    rw [nativeLieLowerCentralModel_zero]
    trivial
  have hp := nativeLieDexpDefect_pow_mem_lowerCentral v hw (Group.nilpotencyClass G)
  rw [Nat.zero_add, nativeLieLowerCentralModel_nilpotencyClass_bot] at hp
  exact hp

noncomputable def nativeLieDexpFiniteInverse (v : E) : E →L[ℝ] E :=
  ∑ n ∈ range (Group.nilpotencyClass G), nativeLieDexpDefect (I := I) (G := G) v ^ n

 theorem nativeLieDexp_mul_finiteInverse (v : E) :
    nativeLieDexp (I := I) (G := G) v * nativeLieDexpFiniteInverse (I := I) (G := G) v = 1 := by
  let W : E →L[ℝ] E := nativeLieDexpDefect (I := I) (G := G) v
  have h := mul_neg_geom_sum W (Group.nilpotencyClass G)
  have hW : W ^ Group.nilpotencyClass G = 0 := nativeLieDexpDefect_pow_nilpotencyClass v
  have hD : 1 - W = nativeLieDexp (I := I) (G := G) v := by
    dsimp [W, nativeLieDexpDefect]
    abel
  rw [hW, sub_zero, hD] at h
  exact h

 theorem nativeLieDexp_finiteInverse_mul (v : E) :
    nativeLieDexpFiniteInverse (I := I) (G := G) v * nativeLieDexp (I := I) (G := G) v = 1 := by
  let W : E →L[ℝ] E := nativeLieDexpDefect (I := I) (G := G) v
  have h := geom_sum_mul_neg W (Group.nilpotencyClass G)
  have hW : W ^ Group.nilpotencyClass G = 0 := nativeLieDexpDefect_pow_nilpotencyClass v
  have hD : 1 - W = nativeLieDexp (I := I) (G := G) v := by
    dsimp [W, nativeLieDexpDefect]
    abel
  rw [hW, sub_zero, hD] at h
  exact h

end Hindman168
