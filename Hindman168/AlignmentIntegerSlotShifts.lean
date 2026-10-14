import Hindman168.AlignmentMasterResidueData

namespace Hindman168
open scoped BigOperators Classical

noncomputable def alignmentIntegerSlotShift {n : ℕ} {i : Fin n}
    (ρ : AlignmentAddingPair n i → ℕ) (v : AlignmentAddingPair n i → ℤ) : ℤ :=
  letI := alignmentAddingPairFintype n i
  ∑ e, v e * ρ e

noncomputable def alignmentIntegerSlotWeight {n : ℕ} {i : Fin n}
    (v : AlignmentAddingPair n i → ℤ) : ℤ :=
  letI := alignmentAddingPairFintype n i
  ∑ e, |v e|

theorem alignmentIntegerSlotShift_zero {n : ℕ} {i : Fin n}
    (ρ : AlignmentAddingPair n i → ℕ) : alignmentIntegerSlotShift ρ 0 = 0 := by
  simp [alignmentIntegerSlotShift]

theorem alignmentIntegerSlotShift_add {n : ℕ} {i : Fin n}
    (ρ : AlignmentAddingPair n i → ℕ) (v u : AlignmentAddingPair n i → ℤ) :
    alignmentIntegerSlotShift ρ (v + u) =
      alignmentIntegerSlotShift ρ v + alignmentIntegerSlotShift ρ u := by
  simp only [alignmentIntegerSlotShift, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem alignmentIntegerSlotShift_unit {n : ℕ} {i : Fin n}
    (ρ : AlignmentAddingPair n i → ℕ) (v : AlignmentAddingPair n i → ℤ)
    (e : AlignmentAddingPair n i) (m : ℤ) :
    alignmentIntegerSlotShift ρ (v + alignmentAuxiliaryUnit e m) =
      alignmentIntegerSlotShift ρ v + m * ρ e := by
  rw [alignmentIntegerSlotShift_add]
  simp [alignmentIntegerSlotShift, alignmentAuxiliaryUnit, ite_mul]

theorem alignmentIntegerSlotShift_divisible {n : ℕ} {i : Fin n}
    (ρ : AlignmentAddingPair n i → ℕ) (v : AlignmentAddingPair n i → ℤ)
    (W : ℕ) (hρ : ∀ e, W ∣ ρ e) : (W : ℤ) ∣ alignmentIntegerSlotShift ρ v := by
  letI := alignmentAddingPairFintype n i
  unfold alignmentIntegerSlotShift
  apply Finset.dvd_sum
  intro e _
  have h : (W : ℤ) ∣ (ρ e : ℤ) := by exact_mod_cast hρ e
  exact dvd_mul_of_dvd_right h _

theorem alignmentIntegerSlotShift_bound {n : ℕ} {i : Fin n}
    (ρ : AlignmentAddingPair n i → ℕ) (v : AlignmentAddingPair n i → ℤ)
    (L : ℕ) (hρ : ∀ e, ρ e ≤ L) :
    |alignmentIntegerSlotShift ρ v| ≤ (L : ℤ) * alignmentIntegerSlotWeight v := by
  letI := alignmentAddingPairFintype n i
  unfold alignmentIntegerSlotShift alignmentIntegerSlotWeight
  calc
    _ ≤ ∑ e, |v e * (ρ e : ℤ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, |v e| * (L : ℤ) := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (ρ e) : (0 : ℤ) ≤ (ρ e : ℤ))]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hρ e) (abs_nonneg _)
    _ = (L : ℤ) * ∑ e, |v e| := by rw [← Finset.sum_mul]; ring

end Hindman168
