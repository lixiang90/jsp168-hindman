import Hindman168.NilCornerReconstruction

/-! The finite recipe selectors used in Prediction. The piece label may
include both an interval and a residue, and orbits may vary arbitrarily
between pieces. On a cube with one piece label exactly its recipe survives. -/

namespace Hindman168
open scoped BigOperators Classical

variable {ι X P : Type*} [Fintype ι] [TopologicalSpace X] {L : ℕ}

noncomputable def pieceRecipeFactor (piece : ℤ → P) (chooseRecipe : P → Fin L)
    (point : P → ℤ → X) (r : Fin L) (factor : ι → C(X, ℝ)) (j : ι) (y : ℤ) : ℝ :=
  if chooseRecipe (piece y) = r then factor j (point (piece y) y) else 0

noncomputable def pieceRecipeCubeSum (recipes : Fin L → CornerProductRecipe ι X)
    (piece : ℤ → P) (chooseRecipe : P → Fin L) (point : P → ℤ → X)
    (vertex : ι → ℤ) : ℝ :=
  ∑ r, ((recipes r).map (fun t => t.1 * ∏ j,
    pieceRecipeFactor piece chooseRecipe point r t.2 j (vertex j))).sum

omit [Fintype ι] in
theorem pieceRecipeFactor_abs_le (piece : ℤ → P) (chooseRecipe : P → Fin L)
    (point : P → ℤ → X) (r : Fin L) (factor : ι → C(X, ℝ))
    (hb : ∀ j x, |factor j x| ≤ 1) (j : ι) (y : ℤ) :
    |pieceRecipeFactor piece chooseRecipe point r factor j y| ≤ 1 := by
  unfold pieceRecipeFactor
  split_ifs
  · exact hb _ _
  · norm_num

omit [Fintype ι] in
theorem pieceRecipeFactor_on_piece (piece : ℤ → P) (chooseRecipe : P → Fin L)
    (point : P → ℤ → X) (r : Fin L) (factor : ι → C(X, ℝ))
    (p : P) (j : ι) (y : ℤ) (hy : piece y = p) :
    pieceRecipeFactor piece chooseRecipe point r factor j y =
      if chooseRecipe p = r then factor j (point p y) else 0 := by
  simp only [pieceRecipeFactor, hy]

theorem pieceRecipeProduct_on_piece [Nonempty ι] (piece : ℤ → P)
    (chooseRecipe : P → Fin L) (point : P → ℤ → X) (r : Fin L)
    (factor : ι → C(X, ℝ)) (p : P) (vertex : ι → ℤ)
    (hp : ∀ j, piece (vertex j) = p) :
    (∏ j, pieceRecipeFactor piece chooseRecipe point r factor j (vertex j)) =
      if chooseRecipe p = r then ∏ j, factor j (point p (vertex j)) else 0 := by
  simp only [pieceRecipeFactor, hp]
  by_cases h : chooseRecipe p = r
  · simp only [if_pos h]
  · simp only [if_neg h]
    obtain ⟨j⟩ := ‹Nonempty ι›
    exact Finset.prod_eq_zero (Finset.mem_univ j) rfl

theorem pieceRecipeCubeSum_on_piece [Nonempty ι]
    (recipes : Fin L → CornerProductRecipe ι X) (piece : ℤ → P)
    (chooseRecipe : P → Fin L) (point : P → ℤ → X) (p : P) (vertex : ι → ℤ)
    (hp : ∀ j, piece (vertex j) = p) :
    pieceRecipeCubeSum recipes piece chooseRecipe point vertex =
      (recipes (chooseRecipe p)).value (fun j => point p (vertex j)) := by
  unfold pieceRecipeCubeSum CornerProductRecipe.value
  rw [Finset.sum_eq_single (chooseRecipe p)]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro t _
    rw [pieceRecipeProduct_on_piece piece chooseRecipe point _ t.2 p vertex hp, if_pos rfl]
  · intro r _ hr
    have hne : chooseRecipe p ≠ r := Ne.symm hr
    have hzero : (recipes r).map (fun t => t.1 * ∏ j,
        pieceRecipeFactor piece chooseRecipe point r t.2 j (vertex j)) =
        (recipes r).map (fun _ => (0 : ℝ)) := by
      apply List.map_congr_left
      intro t _
      rw [pieceRecipeProduct_on_piece piece chooseRecipe point r t.2 p vertex hp, if_neg hne, mul_zero]
    rw [hzero]
    simp
  · simp

theorem pieceRecipeCubeSum_abs_le (recipes : Fin L → CornerProductRecipe ι X)
    (hb : ∀ r, CornerProductRecipe.Bounded (recipes r))
    (piece : ℤ → P) (chooseRecipe : P → Fin L) (point : P → ℤ → X) (vertex : ι → ℤ) :
    |pieceRecipeCubeSum recipes piece chooseRecipe point vertex| ≤
      ∑ r, (recipes r).coefficientMass := by
  unfold pieceRecipeCubeSum
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro r _
  have hbound (s : CornerProductRecipe ι X) (hs : s.Bounded) :
      |(s.map (fun t => t.1 * ∏ j,
        pieceRecipeFactor piece chooseRecipe point r t.2 j (vertex j))).sum| ≤ s.coefficientMass := by
    induction s with
    | nil => simp [CornerProductRecipe.coefficientMass]
    | cons t s ih =>
      have hp : |∏ j, pieceRecipeFactor piece chooseRecipe point r t.2 j (vertex j)| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
          (fun j _ => pieceRecipeFactor_abs_le piece chooseRecipe point r t.2
            (hs t (by simp)) j _)
      have htail : CornerProductRecipe.Bounded s := fun u hu => hs u (by simp [hu])
      simp only [List.map_cons, List.sum_cons, CornerProductRecipe.coefficientMass]
      exact (abs_add_le _ _).trans (add_le_add
        (by rw [abs_mul]; exact (mul_le_mul_of_nonneg_left hp (abs_nonneg t.1)).trans_eq (mul_one _))
        (ih htail))
  exact hbound (recipes r) (hb r)

end Hindman168
