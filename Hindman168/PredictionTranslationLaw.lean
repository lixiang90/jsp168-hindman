import Hindman168.PredictionTranslationCoordinates
import Hindman168.FiniteCoordinateTranslation
import Hindman168.HarmonicTranslation
import Hindman168.UniformIntervalTranslation

/-!
# Original harmonic root and uniform shift law: insertion error

This is an estimate for the concrete independent original column law.
The root requires an actual W-multiple displacement, not merely a smooth
modulus. Each replica retains its own original shift length and its own
auxiliary length; no single common scale is imposed on different gaps.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def predictionOriginalColumnMass {b d : ℕ}
    (X W : ℕ) (A : Fin b × Fin d × Bool → ℤ) (T : Fin b → ℕ) :
    ReplicaCubeColumn b d → Mass ℤ
  | none => integerMass X W
  | some (q, j, bit) => uniformIntervalMass (A (q, j, bit)) (T q)

theorem predictionOriginalColumnMass_nonneg {b d : ℕ}
    (X W : ℕ) (A : Fin b × Fin d × Bool → ℤ) (T : Fin b → ℕ)
    (hZ : 0 < harmonicNormalizer X W) :
    ∀ col z, 0 ≤ predictionOriginalColumnMass X W A T col z := by
  intro col z
  cases col with
  | none => exact integerMass_nonneg hZ z
  | some c => exact uniformIntervalMass_nonneg _ _ z

theorem predictionOriginalColumnMass_total {b d : ℕ}
    (X W : ℕ) (A : Fin b × Fin d × Bool → ℤ) (T : Fin b → ℕ)
    (hZ : 0 < harmonicNormalizer X W) (hT : ∀ q, 0 < T q) :
    ∀ col, total (predictionOriginalColumnMass X W A T col) = 1 := by
  intro col
  cases col with
  | none => exact integerMass_total hZ
  | some c => exact uniformIntervalMass_total _ (hT c.1)

noncomputable def predictionInsertionErrorCap {b d h : ℕ}
    (X W : ℕ) (T : Fin b → ℕ) (dir : Fin h → Fin b × CubeVertex d)
    (R L : Fin b → ℝ) : ℝ :=
  2 * (∑ i, |(cubeRootDirection (dir i).2.val : ℝ)| * R (dir i).1) /
      ((X : ℝ) * (Real.log X - (W : ℝ) / X)) +
    ∑ q, ∑ j : Fin d, 2 * (h : ℝ) * |(cubeShiftDirection j : ℝ)| * L q / T q

theorem prediction_insertion_coordinate_errors {b d h : ℕ}
    (X W : ℕ) (A : Fin b × Fin d × Bool → ℤ) (T : Fin b → ℕ)
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d)
    (t : Fin h → ℤ) (R L : Fin b → ℝ)
    (hX : 2 ≤ X) (hW : 0 < W) (hlog : (W : ℝ) / X < Real.log X)
    (hT : ∀ q, 0 < T q) (hM : ∀ q, (W : ℤ) ∣ M q)
    (hL : ∀ q, 0 ≤ L q) (ht : ∀ i, |(t i : ℝ)| ≤ L (dir i).1)
    (hR : ∀ i, |((M (dir i).1 * t i : ℤ) : ℝ)| ≤ R (dir i).1) :
    (∑ col, distance ((predictionOriginalColumnMass X W A T col).mapDomain
      (fun z => z + predictionInsertedTranslation M dir t col))
      (predictionOriginalColumnMass X W A T col)) ≤
      predictionInsertionErrorCap X W T dir R L := by
  have hden : 0 < (X : ℝ) * (Real.log X - (W : ℝ) / X) := by
    have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    exact mul_pos hXp (sub_pos.mpr hlog)
  unfold predictionInsertionErrorCap
  rw [Fintype.sum_option]
  apply add_le_add
  · change distance ((integerMass X W).mapDomain _) (integerMass X W) ≤ _
    exact ((integer_harmonic_translation_error hX hW hlog
      (predictionInsertedTranslation_root_dvd M dir t W hM)).trans (min_le_right _ _)).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (predictionInsertedTranslation_root_bound M dir t R hR)
          (by norm_num)) hden.le)
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    apply Finset.sum_le_sum
    intro q _
    apply Finset.sum_le_sum
    intro j _
    simp only [predictionOriginalColumnMass]
    have hz : distance ((uniformIntervalMass (A (q, j, false)) (T q)).mapDomain
        (fun z => z + predictionInsertedTranslation M dir t (some (q, j, false))))
        (uniformIntervalMass (A (q, j, false)) (T q)) = 0 := by
      rw [predictionInsertedTranslation_false]
      simp only [add_zero]
      change distance ((uniformIntervalMass (A (q, j, false)) (T q)).mapDomain id)
        (uniformIntervalMass (A (q, j, false)) (T q)) = 0
      rw [Finsupp.mapDomain_id]
      simp [distance, variation]
    rw [hz, add_zero]
    change distance ((uniformIntervalMass (A (q, j, true)) (T q)).mapDomain
      (fun z => z + predictionInsertedTranslation M dir t (some (q, j, true))))
      (uniformIntervalMass (A (q, j, true)) (T q)) ≤ _
    have hb := predictionInsertedTranslation_true_bound M dir t L hL ht q j
    have he := uniform_interval_translation_linear (A (q, j, true)) (hT q)
      (predictionInsertedTranslation M dir t (some (q, j, true)))
    refine he.trans ?_
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hm := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
    convert hm using 1; first | rfl | ring

theorem prediction_insertion_expectation_error {b d h : ℕ}
    (X W : ℕ) (A : Fin b × Fin d × Bool → ℤ) (T : Fin b → ℕ)
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d)
    (t : Fin h → ℤ) (R L : Fin b → ℝ)
    (G : ReplicaCubeRow b d → ℤ → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hG : ∀ base y, |G base y| ≤ B)
    (hX : 2 ≤ X) (hW : 0 < W) (hlog : (W : ℝ) / X < Real.log X)
    (hT : ∀ q, 0 < T q) (hM : ∀ q, (W : ℤ) ∣ M q)
    (hL : ∀ q, 0 ≤ L q) (ht : ∀ i, |(t i : ℝ)| ≤ L (dir i).1)
    (hR : ∀ i, |((M (dir i).1 * t i : ℤ) : ℝ)| ≤ R (dir i).1) :
    |expectation (piMass (predictionOriginalColumnMass X W A T))
        (fun z => ∏ base, G base (replicaCubeEval M base
          (fun col => z col + predictionInsertedTranslation M dir t col))) -
      expectation (piMass (predictionOriginalColumnMass X W A T))
        (fun z => ∏ base, G base (replicaCubeEval M base z))| ≤
      B ^ Fintype.card (ReplicaCubeRow b d) * predictionInsertionErrorCap X W T dir R L := by
  have hZ := harmonicNormalizer_pos hX hW hlog
  have hb (z : ReplicaCubeColumn b d → ℤ) :
      |∏ base, G base (replicaCubeEval M base z)| ≤ B ^ Fintype.card (ReplicaCubeRow b d) := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _base : ReplicaCubeRow b d, B := Finset.prod_le_prod
        (fun _ _ => abs_nonneg _) (fun base _ => hG base _)
      _ = _ := by simp
  exact (piMass_translation_expectation_bound (predictionOriginalColumnMass X W A T)
    (predictionInsertedTranslation M dir t) (fun z => ∏ base, G base (replicaCubeEval M base z))
    (predictionOriginalColumnMass_nonneg X W A T hZ)
    (predictionOriginalColumnMass_total X W A T hZ hT) (pow_nonneg hB _) hb).trans
      (mul_le_mul_of_nonneg_left
        (prediction_insertion_coordinate_errors X W A T M dir t R L hX hW hlog hT hM hL ht hR)
        (pow_nonneg hB _))

end Hindman168
