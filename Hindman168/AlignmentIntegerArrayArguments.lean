import Hindman168.AlignmentIntegerSlotShifts

/-! The numerical array arguments from the paper. Only an own-target
letter has the numerical translation proved here; no arbitrary jump
is asserted to translate the original pivot orbit. -/

namespace Hindman168
open scoped BigOperators Classical

noncomputable def alignmentIntegerArrayProgression {n : ℕ} {i : Fin n}
    (Δ : AlignmentAddingPair n i → ℤ) (T : Finset (Fin n))
    (u : AlignmentAddingPair n i → ℤ) : ℤ :=
  letI := alignmentAddingPairFintype n i
  ∑ e, if e.targetTail = T then u e * Δ e else 0

noncomputable def alignmentIntegerArrayArgument {n : ℕ} {i : Fin n}
    (t : Fin n → ℕ) (M : ℕ) (ρ : AlignmentAddingPair n i → ℕ)
    (Δ : AlignmentAddingPair n i → ℤ) (T : Finset (Fin n))
    (p : ℤ) (v u : AlignmentAddingPair n i → ℤ) : ℤ :=
  (alignmentNaturalBlockProduct t T : ℤ) * (p + alignmentIntegerSlotShift ρ v) +
    (M : ℤ) * alignmentIntegerArrayProgression Δ T u

theorem alignmentIntegerArrayProgression_add {n : ℕ} {i : Fin n}
    (Δ : AlignmentAddingPair n i → ℤ) (T : Finset (Fin n))
    (u v : AlignmentAddingPair n i → ℤ) :
    alignmentIntegerArrayProgression Δ T (u + v) =
      alignmentIntegerArrayProgression Δ T u + alignmentIntegerArrayProgression Δ T v := by
  unfold alignmentIntegerArrayProgression
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : e.targetTail = T
  · rw [if_pos h, if_pos h, if_pos h]
    exact add_mul (u e) (v e) (Δ e)
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

theorem alignmentIntegerArrayProgression_unit {n : ℕ} {i : Fin n}
    (Δ : AlignmentAddingPair n i → ℤ) (T : Finset (Fin n))
    (e : AlignmentAddingPair n i) (he : e.targetTail = T) (m : ℤ) :
    alignmentIntegerArrayProgression Δ T (alignmentAuxiliaryUnit e m) = m * Δ e := by
  letI := alignmentAddingPairFintype n i
  unfold alignmentIntegerArrayProgression
  calc
    _ = ∑ f, if f = e then m * Δ e else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      by_cases h : f = e
      · subst f; simp [alignmentAuxiliaryUnit, he]
      · simp [alignmentAuxiliaryUnit, h]
    _ = _ := by simp

theorem alignmentIntegerArrayArgument_own_letter {n : ℕ} {i : Fin n}
    (t : Fin n → ℕ) (M : ℕ) (ρ : AlignmentAddingPair n i → ℕ)
    (Δ : AlignmentAddingPair n i → ℤ) (Q : AlignmentAddingPair n i → ℕ)
    (T : Finset (Fin n)) (e : AlignmentAddingPair n i) (he : e.targetTail = T)
    (hexact : (M : ℤ) * Δ e = (Q e : ℤ) -
      (alignmentNaturalBlockProduct t T : ℤ) * ρ e)
    (p m : ℤ) (v u : AlignmentAddingPair n i → ℤ) :
    alignmentIntegerArrayArgument t M ρ Δ T p
        (v + alignmentAuxiliaryUnit e m) (u + alignmentAuxiliaryUnit e m) =
      alignmentIntegerArrayArgument t M ρ Δ T p v u + m * Q e := by
  unfold alignmentIntegerArrayArgument
  rw [alignmentIntegerSlotShift_unit, alignmentIntegerArrayProgression_add,
    alignmentIntegerArrayProgression_unit Δ T e he]
  have htotal : (alignmentNaturalBlockProduct t T : ℤ) * ρ e + (M : ℤ) * Δ e = Q e := by
    linear_combination hexact
  calc
    _ = (alignmentNaturalBlockProduct t T : ℤ) * (p + alignmentIntegerSlotShift ρ v) +
      (M : ℤ) * alignmentIntegerArrayProgression Δ T u +
      m * ((alignmentNaturalBlockProduct t T : ℤ) * ρ e + (M : ℤ) * Δ e) := by ring
    _ = _ := by rw [htotal]

end Hindman168
