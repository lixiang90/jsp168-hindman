import Hindman168.PredictionInitialStage

/-!
# Total displacement of the actual inserted cube directions

All directions are inserted at once. Their root displacement is a
multiple of W when every actual replica modulus is. False shift columns
remain unchanged; true shift columns have a bound using only their own
replica's auxiliary length. Different gaps need no common direction scale.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def predictionInsertedTranslation {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d)
    (t : Fin h → ℤ) (col : ReplicaCubeColumn b d) : ℤ :=
  ∑ i, t i * replicaCubeDirection M (dir i).1 (dir i).2 col

theorem predictionInsertedTranslation_root {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (t : Fin h → ℤ) :
    predictionInsertedTranslation M dir t none =
      ∑ i, t i * cubeRootDirection (dir i).2.val * M (dir i).1 := by
  simp only [predictionInsertedTranslation, replicaCubeDirection, mul_assoc]

theorem predictionInsertedTranslation_false {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d)
    (t : Fin h → ℤ) (q : Fin b) (j : Fin d) :
    predictionInsertedTranslation M dir t (some (q, j, false)) = 0 := by
  simp only [predictionInsertedTranslation, replicaCubeDirection, Bool.false_eq_true,
    and_false, ite_false, mul_zero, Finset.sum_const_zero]

theorem predictionInsertedTranslation_true {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d)
    (t : Fin h → ℤ) (q : Fin b) (j : Fin d) :
    predictionInsertedTranslation M dir t (some (q, j, true)) =
      cubeShiftDirection j * ∑ i, if (dir i).1 = q then t i else 0 := by
  simp only [predictionInsertedTranslation, replicaCubeDirection, and_true, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hq : (dir i).1 = q
  · simp [hq, mul_comm]
  · simp [hq, Ne.symm hq]

theorem predictionInsertedTranslation_root_dvd {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d)
    (t : Fin h → ℤ) (W : ℕ) (hW : ∀ q, (W : ℤ) ∣ M q) :
    (W : ℤ) ∣ predictionInsertedTranslation M dir t none := by
  rw [predictionInsertedTranslation_root]
  exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hW (dir i).1) _)

theorem predictionInsertedTranslation_root_bound {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d)
    (t : Fin h → ℤ) (R : Fin b → ℝ)
    (hR : ∀ i, |((M (dir i).1 * t i : ℤ) : ℝ)| ≤ R (dir i).1) :
    |(predictionInsertedTranslation M dir t none : ℝ)| ≤
      ∑ i, |(cubeRootDirection (dir i).2.val : ℝ)| * R (dir i).1 := by
  rw [predictionInsertedTranslation_root, Int.cast_sum]
  calc
    _ ≤ ∑ i, |((t i * cubeRootDirection (dir i).2.val * M (dir i).1 : ℤ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have he : ((t i * cubeRootDirection (dir i).2.val * M (dir i).1 : ℤ) : ℝ) =
          (cubeRootDirection (dir i).2.val : ℝ) * ((M (dir i).1 * t i : ℤ) : ℝ) := by
        push_cast
        ring
      rw [he, abs_mul]
      exact mul_le_mul_of_nonneg_left (hR i) (abs_nonneg _)

theorem predictionInsertedTranslation_true_bound {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d)
    (t : Fin h → ℤ) (L : Fin b → ℝ) (hL : ∀ q, 0 ≤ L q)
    (ht : ∀ i, |(t i : ℝ)| ≤ L (dir i).1) (q : Fin b) (j : Fin d) :
    |(predictionInsertedTranslation M dir t (some (q, j, true)) : ℝ)| ≤
      (h : ℝ) * |(cubeShiftDirection j : ℝ)| * L q := by
  rw [predictionInsertedTranslation_true, Int.cast_mul, Int.cast_sum, abs_mul]
  have hs : |∑ i, ((if (dir i).1 = q then t i else 0 : ℤ) : ℝ)| ≤ (h : ℝ) * L q := by
    calc
      _ ≤ ∑ i, |((if (dir i).1 = q then t i else 0 : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin h, L q := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hq
        · simpa only [hq] using ht i
        · simpa only [Int.cast_zero, abs_zero] using hL q
      _ = _ := by simp
  have hm := mul_le_mul_of_nonneg_left hs (abs_nonneg (cubeShiftDirection j : ℝ))
  calc
    _ ≤ |(cubeShiftDirection j : ℝ)| * ((h : ℝ) * L q) := hm
    _ = _ := by ring

end Hindman168
