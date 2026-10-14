import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Hindman168
open scoped BigOperators Classical

def positiveNaturalLags (N : ℕ) : Finset ℕ := (Finset.range N).filter (fun h => 0 < h)

theorem positive_natural_lags_mem (N h : ℕ) :
    h ∈ positiveNaturalLags N ↔ h < N ∧ 0 < h := by
  simp only [positiveNaturalLags, Finset.mem_filter, Finset.mem_range]

theorem positive_natural_lags_card_le (N : ℕ) : (positiveNaturalLags N).card ≤ N := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)

/-- Reindex actual ordered pairs i<j by their actual positive lag j-i. -/
theorem finite_positive_lag_reindex {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → M) :
    (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j, F j i) =
      ∑ h ∈ positiveNaturalLags N, ∑ i ∈ Finset.range (N-h), F (i+h) i := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij'
    (fun p _ => (⟨p.1-p.2, p.2⟩ : Σ _ : ℕ, ℕ))
    (fun p _ => (⟨p.2+p.1, p.2⟩ : Σ _ : ℕ, ℕ))
  · intro p hp
    have h := Finset.mem_sigma.mp hp
    have hj := Finset.mem_range.mp h.1
    have hi := Finset.mem_range.mp h.2
    apply Finset.mem_sigma.mpr
    constructor
    · apply (positive_natural_lags_mem _ _).mpr
      change p.1-p.2 < N ∧ 0 < p.1-p.2
      constructor <;> omega
    · apply Finset.mem_range.mpr
      dsimp
      omega
  · intro p hp
    have h := Finset.mem_sigma.mp hp
    have hh := (positive_natural_lags_mem _ _).mp h.1
    have hi := Finset.mem_range.mp h.2
    apply Finset.mem_sigma.mpr
    constructor <;> apply Finset.mem_range.mpr <;> dsimp <;> omega
  · intro p hp
    have h := Finset.mem_sigma.mp hp
    have hi := Finset.mem_range.mp h.2
    have he : p.2+(p.1-p.2) = p.1 := by omega
    dsimp
    rw [he]
  · intro p hp
    dsimp
    simp only [Nat.add_sub_cancel_left]
  · intro p hp
    have h := Finset.mem_sigma.mp hp
    have hi := Finset.mem_range.mp h.2
    dsimp
    rw [show p.2+(p.1-p.2)=p.1 by omega]

end Hindman168
