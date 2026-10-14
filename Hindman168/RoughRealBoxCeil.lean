import Hindman168.RoughCorrectedBoxCubeSelection
import Hindman168.AlignmentCeilBoxes

namespace Hindman168
open scoped BigOperators Classical

noncomputable def roughRealIntegerBox {κ : Type*} [Fintype κ]
    (lo hi : κ → ℝ) : Finset (κ → ℤ) :=
  Fintype.piFinset (fun j => Finset.Ico ⌈lo j⌉ ⌈hi j⌉)

noncomputable def roughRealBoxWidths {κ : Type*} (lo hi : κ → ℝ) : κ → ℕ :=
  fun j => (⌈hi j⌉-⌈lo j⌉).toNat

theorem rough_real_integer_box_mem {κ : Type*} [Fintype κ]
    (lo hi : κ → ℝ) (x : κ → ℤ) :
    x ∈ roughRealIntegerBox lo hi ↔ ∀ j, lo j ≤ (x j : ℝ) ∧ (x j : ℝ) < hi j := by
  simp only [roughRealIntegerBox, Fintype.mem_piFinset, alignment_ceil_interval_mem]

theorem rough_real_integer_box_width_representation {κ : Type*} [Fintype κ]
    (lo hi : κ → ℝ) (hlohi : ∀ j, lo j ≤ hi j) :
    roughRealIntegerBox lo hi =
      roughIntegerWidthBox (fun j => ⌈lo j⌉) (roughRealBoxWidths lo hi) := by
  unfold roughRealIntegerBox roughIntegerWidthBox roughRealBoxWidths
  congr 1
  funext j
  have hj := Int.ceil_mono (hlohi j)
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hj), add_sub_cancel]

theorem rough_real_integer_box_scaled_bounds {κ : Type*}
    (lo hi : κ → ℝ) (c C Z : ℝ) (hc : 0 < c) (hZ : 1 ≤ Z)
    (hlarge : 2 ≤ c*Z) (hlen : ∀ j, c*Z ≤ hi j-lo j)
    (hlo : ∀ j, -C*Z ≤ lo j) (hhi : ∀ j, hi j ≤ C*Z) :
    (∀ j, (c/2)*Z ≤ (roughRealBoxWidths lo hi j : ℝ)) ∧
    (∀ j, -(C+1)*Z ≤ (⌈lo j⌉ : ℝ)) ∧
    (∀ j, (⌈lo j⌉ : ℝ)+(roughRealBoxWidths lo hi j : ℝ) ≤ (C+1)*Z) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have horder : ∀ j, lo j ≤ hi j := fun j => by
    have hp := mul_pos hc hZ0
    linarith [hlen j]
  have hwidth : ∀ j, (roughRealBoxWidths lo hi j : ℝ) = (⌈hi j⌉ : ℝ)-(⌈lo j⌉ : ℝ) := by
    intro j
    have hj := Int.ceil_mono (horder j)
    have hh := Int.toNat_of_nonneg (sub_nonneg.mpr hj)
    dsimp [roughRealBoxWidths]
    exact_mod_cast hh
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rw [hwidth j]
    exact (alignment_ceil_side_bounds (lo j) (hi j) Z c C hZ hlarge (hlen j) (hlo j) (hhi j)).1
  · intro j
    have hj := Int.le_ceil (lo j)
    nlinarith [hlo j]
  · intro j
    rw [hwidth j]
    have hj := Int.ceil_lt_add_one (hi j)
    nlinarith [hhi j]

end Hindman168
