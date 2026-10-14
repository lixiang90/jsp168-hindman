import Hindman168.RoughEqualTiledBoxGeometry
import Hindman168.RoughProductBoundaryFraction

namespace Hindman168
open scoped BigOperators Classical

theorem rough_equal_box_boundary_fraction {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) (N : ℕ) (hwidth : ∀ j, 0 < width j) :
    (((roughIntegerWidthBox a width \ roughEqualTiledBox a width N).card : ℝ)/
      (roughIntegerWidthBox a width).card) ≤ ∑ j, ((width j%N : ℕ) : ℝ)/(width j : ℝ) := by
  have hsub := rough_equal_tiled_box_contained a width N
  have hcard := Finset.card_le_card hsub
  have hS : (0 : ℝ) < (roughIntegerWidthBox a width).card := by
    exact_mod_cast (rough_integer_width_box_nonempty a width hwidth).card_pos
  have hlen : ∀ j, N*(width j/N) ≤ width j := by
    intro j
    have hmod := Nat.mod_add_div (width j) N
    omega
  have hwr : ∀ j, (0 : ℝ) < width j := fun j => by exact_mod_cast hwidth j
  have hid : ∀ j, 1-((N*(width j/N) : ℕ) : ℝ)/(width j : ℝ) =
      ((width j%N : ℕ) : ℝ)/(width j : ℝ) := by
    intro j
    have hm : ((width j%N : ℕ) : ℝ)+((N*(width j/N) : ℕ) : ℝ) = (width j : ℝ) := by
      exact_mod_cast Nat.mod_add_div (width j) N
    apply (eq_div_iff (hwr j).ne').mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (hwr j).ne']
    linarith
  calc
    _ = 1-((roughEqualTiledBox a width N).card : ℝ)/(roughIntegerWidthBox a width).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Nat.cast_sub hcard]
      field_simp [hS.ne']
    _ = 1-∏ j, ((N*(width j/N) : ℕ) : ℝ)/(width j : ℝ) := by
      rw [rough_equal_tiled_box_card, rough_integer_width_box_card,
        Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]
    _ ≤ ∑ j, (1-((N*(width j/N) : ℕ) : ℝ)/(width j : ℝ)) := by
      apply rough_finite_product_deficit
      · intro j _
        positivity
      · intro j _
        apply (div_le_one (hwr j)).mpr
        exact_mod_cast hlen j
    _ = _ := Finset.sum_congr rfl (fun j _ => hid j)

theorem rough_equal_box_boundary_fraction_side {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) (N : ℕ) (hN : 0 < N)
    (hwidth : ∀ j, 0 < width j) :
    (((roughIntegerWidthBox a width \ roughEqualTiledBox a width N).card : ℝ)/
      (roughIntegerWidthBox a width).card) ≤ ∑ j, (N : ℝ)/(width j : ℝ) := by
  apply (rough_equal_box_boundary_fraction a width N hwidth).trans
  apply Finset.sum_le_sum
  intro j _
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (Nat.mod_lt (width j) hN).le

end Hindman168
