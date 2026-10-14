import Hindman168.RoughEqualIntervalCoordinates

namespace Hindman168
open scoped BigOperators Classical

noncomputable def roughIntegerWidthBox {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) : Finset (κ → ℤ) :=
  Fintype.piFinset (fun j => Finset.Ico (a j) (a j+width j))

def roughEqualCubeOrigin {κ : Type*} (a : κ → ℤ) (N : ℕ) (r : κ → ℕ) : κ → ℤ :=
  fun j => a j+(N*r j : ℕ)

noncomputable def roughEqualCube {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (N : ℕ) (r : κ → ℕ) : Finset (κ → ℤ) :=
  roughIntegerWidthBox (roughEqualCubeOrigin a N r) (fun _ => N)

noncomputable def roughEqualTiledBox {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) (N : ℕ) : Finset (κ → ℤ) :=
  roughIntegerWidthBox a (fun j => N*(width j/N))

def roughEqualCubeLabel {κ : Type*} (a : κ → ℤ) (width : κ → ℕ) (N : ℕ)
    (hN : 0 < N) (hwidth : ∀ j, N ≤ width j) (x : κ → ℤ) :
    ∀ j, Fin (width j/N) := fun j =>
  if h : (x j-a j).toNat/N < width j/N then ⟨(x j-a j).toNat/N, h⟩
  else ⟨0, Nat.div_pos (hwidth j) hN⟩

theorem rough_equal_cube_interval {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (N : ℕ) (r : κ → ℕ) :
    roughEqualCube a N r =
      Fintype.piFinset (fun j => Finset.Ico (a j+(N*r j : ℕ)) (a j+(N*(r j+1) : ℕ))) := by
  unfold roughEqualCube roughIntegerWidthBox roughEqualCubeOrigin
  congr 1
  funext j
  congr 1
  push_cast
  ring

theorem rough_integer_width_box_card {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) :
    (roughIntegerWidthBox a width).card = ∏ j, width j := by
  simp [roughIntegerWidthBox, Fintype.card_piFinset, Int.card_Ico]

theorem rough_equal_cube_card {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (N : ℕ) (r : κ → ℕ) :
    (roughEqualCube a N r).card = N^(Fintype.card κ) := by
  simp [roughEqualCube, rough_integer_width_box_card]

end Hindman168
