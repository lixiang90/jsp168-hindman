import Hindman168.RoughEqualCubeFibers

namespace Hindman168
open scoped BigOperators Classical

theorem rough_integer_width_box_nonempty {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) (hwidth : ∀ j, 0 < width j) :
    (roughIntegerWidthBox a width).Nonempty := by
  refine ⟨a, Fintype.mem_piFinset.mpr ?_⟩
  intro j
  have hw : (0 : ℤ) < width j := by exact_mod_cast hwidth j
  exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩

theorem rough_equal_tiled_box_contained {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) (N : ℕ) :
    roughEqualTiledBox a width N ⊆ roughIntegerWidthBox a width := by
  intro x hx
  apply Fintype.mem_piFinset.mpr
  intro j
  have hj := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hx j)
  change a j ≤ x j ∧ x j < a j+((N*(width j/N) : ℕ) : ℤ) at hj
  have hmod := Nat.mod_add_div (width j) N
  have hlen : N*(width j/N) ≤ width j := by omega
  have hlenZ : ((N*(width j/N) : ℕ) : ℤ) ≤ width j := by exact_mod_cast hlen
  exact Finset.mem_Ico.mpr ⟨hj.1, by omega⟩

theorem rough_equal_tiled_box_nonempty {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) (N : ℕ) (hN : 0 < N)
    (hwidth : ∀ j, N ≤ width j) : (roughEqualTiledBox a width N).Nonempty := by
  apply rough_integer_width_box_nonempty
  intro j
  exact Nat.mul_pos hN (Nat.div_pos (hwidth j) hN)

theorem rough_equal_tiled_box_card {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) (N : ℕ) :
    (roughEqualTiledBox a width N).card = ∏ j, N*(width j/N) :=
  rough_integer_width_box_card _ _

theorem rough_equal_cube_nonempty {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (N : ℕ) (hN : 0 < N) (r : κ → ℕ) :
    (roughEqualCube a N r).Nonempty :=
  rough_integer_width_box_nonempty _ _ (fun _ => hN)

end Hindman168
