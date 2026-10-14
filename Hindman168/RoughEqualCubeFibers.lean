import Hindman168.RoughEqualCubeDefinitions

namespace Hindman168
open scoped BigOperators Classical

theorem rough_equal_cube_label_val {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) (N : ℕ) (hN : 0 < N)
    (hwidth : ∀ j, N ≤ width j) (x : κ → ℤ)
    (hx : x ∈ roughEqualTiledBox a width N) (j : κ) :
    (roughEqualCubeLabel a width N hN hwidth x j).val = (x j-a j).toNat/N := by
  have hj := Fintype.mem_piFinset.mp hx j
  have hj' := Finset.mem_Ico.mp hj
  change a j ≤ x j ∧ x j < a j+((N*(width j/N) : ℕ) : ℤ) at hj'
  have hkZ : (((x j-a j).toNat : ℕ) : ℤ) = x j-a j := Int.toNat_of_nonneg (by omega)
  have hk : (x j-a j).toNat < N*(width j/N) := by
    have h : (((x j-a j).toNat : ℕ) : ℤ) < ((N*(width j/N) : ℕ) : ℤ) := by omega
    exact_mod_cast h
  have hq : (x j-a j).toNat/N < width j/N :=
    (Nat.div_lt_iff_lt_mul hN).mpr (by nlinarith)
  simp only [roughEqualCubeLabel, dif_pos hq]

theorem rough_equal_cube_label_fiber {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) (N : ℕ) (hN : 0 < N)
    (hwidth : ∀ j, N ≤ width j) (r : ∀ j, Fin (width j/N)) :
    (roughEqualTiledBox a width N).filter
      (fun x => roughEqualCubeLabel a width N hN hwidth x = r) =
        roughEqualCube a N (fun j => (r j).val) := by
  ext x
  rw [Finset.mem_filter, rough_equal_cube_interval, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hx, he⟩ j
    have hq := rough_equal_cube_label_val a width N hN hwidth x hx j
    have hr := congrArg Fin.val (congrFun he j)
    rw [hr] at hq
    exact (rough_equal_interval_tiled_coordinate_iff (a j) (width j) N (r j).val
      hN (r j).isLt (x j)).mp ⟨Fintype.mem_piFinset.mp hx j, hq.symm⟩
  · intro hx
    have hcoords := fun j => (rough_equal_interval_tiled_coordinate_iff (a j) (width j) N
      (r j).val hN (r j).isLt (x j)).mpr (hx j)
    have hT : x ∈ roughEqualTiledBox a width N :=
      Fintype.mem_piFinset.mpr (fun j => (hcoords j).1)
    refine ⟨hT, ?_⟩
    funext j
    apply Fin.ext
    rw [rough_equal_cube_label_val a width N hN hwidth x hT j]
    exact (hcoords j).2

theorem rough_equal_cube_contained {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) (N : ℕ) (r : ∀ j, Fin (width j/N)) :
    roughEqualCube a N (fun j => (r j).val) ⊆ roughIntegerWidthBox a width := by
  rw [rough_equal_cube_interval]
  intro x hx
  apply Fintype.mem_piFinset.mpr
  intro j
  exact rough_equal_interval_tile_contained (a j) (width j) N (r j).val (r j).isLt
    (Fintype.mem_piFinset.mp hx j)

end Hindman168
