import Hindman168.RoughEqualCubeSideFloor

namespace Hindman168
open scoped BigOperators Classical

theorem rough_equal_cube_origin_mem {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (N : ℕ) (hN : 0 < N) (r : κ → ℕ) :
    roughEqualCubeOrigin a N r ∈ roughEqualCube a N r := by
  apply Fintype.mem_piFinset.mpr
  intro j
  have hNr : (0 : ℤ) < N := by exact_mod_cast hN
  exact Finset.mem_Ico.mpr ⟨le_rfl, by
    change roughEqualCubeOrigin a N r j < roughEqualCubeOrigin a N r j+(N : ℤ)
    omega⟩

theorem rough_equal_cube_origin_bound {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) (N : ℕ) (hN : 0 < N)
    (r : ∀ j, Fin (width j/N)) (C Z : ℝ)
    (hlo : ∀ j, -C*Z ≤ (a j : ℝ))
    (hhi : ∀ j, (a j : ℝ)+(width j : ℝ) ≤ C*Z) :
    ∀ j, |(roughEqualCubeOrigin a N (fun j => (r j).val) j : ℝ)| ≤ C*Z := by
  have hm := rough_equal_cube_contained a width N r
    (rough_equal_cube_origin_mem a N hN (fun j => (r j).val))
  intro j
  have hj := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hm j)
  have hleft : (a j : ℝ) ≤ (roughEqualCubeOrigin a N (fun j => (r j).val) j : ℝ) := by
    exact_mod_cast hj.1
  have hright : (roughEqualCubeOrigin a N (fun j => (r j).val) j : ℝ) <
      (a j : ℝ)+(width j : ℝ) := by
    exact_mod_cast hj.2
  apply abs_le.mpr
  constructor
  · linarith [hlo j]
  · linarith [hhi j]

end Hindman168
