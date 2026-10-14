import Hindman168.NativeLieLogarithmAffineLayer

/-! The actual original group adjoint acts as identity modulo the next
native lower-central layer. The positive-power formula is derived from
the actual finite adjoint formula, including nilpotency class zero. -/

namespace Hindman168
open Function Set Finset
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieAdjoint_exponential_sub_one_finite_formula (v : E) :
    (nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) : E →L[ℝ] E) - 1 =
      ∑ n ∈ range (Group.nilpotencyClass G),
        ((n + 1).factorial : ℝ)⁻¹ • nativeLieAdjointGenerator (I := I) (G := G) v ^ (n + 1) := by
  let c := Group.nilpotencyClass G
  let B : E →L[ℝ] E := nativeLieAdjointGenerator (I := I) (G := G) v
  let A : E →L[ℝ] E := nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v)
  let a : ℕ → ℝ := fun n => (n.factorial : ℝ)⁻¹
  have hp : B ^ c = 0 := nativeLieAdjointGenerator_pow_nilpotencyClass v
  have he : (∑ n ∈ range (c + 1), a n • B ^ n) = ∑ n ∈ range c, a n • B ^ n := by
    rw [sum_range_succ, hp, smul_zero, add_zero]
  have hA : A = (∑ n ∈ range c, a (n + 1) • B ^ (n + 1)) + 1 := by
    have hf : A = ∑ n ∈ range c, a n • B ^ n :=
      nativeLieAdjoint_exponential_finite_formula_of_group_isNilpotent v
    rw [hf, ← he, sum_range_succ']
    simp only [a, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  change A - 1 = ∑ n ∈ range c, a (n + 1) • B ^ (n + 1)
  rw [hA]
  abel

 theorem nativeLieAdjoint_exponential_sub_mem_lowerCentral_next
    (v : E) {w : E} {j : ℕ}
    (hw : w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) :
    (nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) : E →L[ℝ] E) w - w ∈
      nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
  let A : E →L[ℝ] E := nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v)
  have he : A - 1 = ∑ n ∈ range (Group.nilpotencyClass G),
      ((n + 1).factorial : ℝ)⁻¹ • nativeLieAdjointGenerator (I := I) (G := G) v ^ (n + 1) :=
    nativeLieAdjoint_exponential_sub_one_finite_formula v
  change A w - w ∈ nativeLieLowerCentralModel (I := I) (G := G) (j + 1)
  have ha : A w - w = (A - 1) w := by simp only [sub_apply, one_apply_eq_self]
  rw [ha, he]
  simp only [_root_.sum_apply, smul_apply]
  apply Submodule.sum_mem
  intro n _
  apply Submodule.smul_mem
  exact nativeLieLowerCentralModel_antitone (I := I) (G := G) (by omega)
    (nativeLieAdjointGenerator_pow_mem_lowerCentral v hw (n + 1))

variable [FiniteDimensional ℝ E] [ConnectedSpace G]

 theorem nativeLieAdjoint_sub_mem_lowerCentral_next
    (g : G) {w : E} {j : ℕ}
    (hw : w ∈ nativeLieLowerCentralModel (I := I) (G := G) j) :
    (nativeLieAdjoint (I := I) g : E →L[ℝ] E) w - w ∈
      nativeLieLowerCentralModel (I := I) (G := G) (j + 1) := by
  obtain ⟨v, rfl⟩ := nativeLieExponential_surjective (E := E) (I := I) (G := G) g
  exact nativeLieAdjoint_exponential_sub_mem_lowerCentral_next (E := E) v hw

end Hindman168
