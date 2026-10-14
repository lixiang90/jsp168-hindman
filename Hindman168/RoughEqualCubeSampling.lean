import Hindman168.RoughEqualTiledBoxGeometry

namespace Hindman168
open scoped BigOperators Classical

theorem rough_equal_cube_sample_injective {κ : Type*}
    (a : κ → ℤ) (N : ℕ) (r : κ → ℕ) :
    Function.Injective (fun v : κ → ℕ => fun j => roughEqualCubeOrigin a N r j+(v j : ℤ)) := by
  intro v w he
  funext j
  have hj := congrFun he j
  have hh : (v j : ℤ) = w j := by linarith
  exact_mod_cast hh

theorem rough_equal_cube_sample_image {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (N : ℕ) (r : κ → ℕ) :
    (Fintype.piFinset (fun _ : κ => Finset.range N)).image
      (fun v => fun j => roughEqualCubeOrigin a N r j+(v j : ℤ)) = roughEqualCube a N r := by
  rw [rough_equal_cube_interval]
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    apply Fintype.mem_piFinset.mpr
    intro j
    have hvj := Finset.mem_range.mp (Fintype.mem_piFinset.mp hv j)
    have hvZ : (v j : ℤ) < N := by exact_mod_cast hvj
    have hv0 : (0 : ℤ) ≤ v j := by positivity
    have he : (a j+(N*(r j+1) : ℕ)) = roughEqualCubeOrigin a N r j+N := by
      simp only [roughEqualCubeOrigin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    rw [he]
    exact Finset.mem_Ico.mpr ⟨by dsimp [roughEqualCubeOrigin]; omega, by omega⟩
  · intro hx
    have hcoords := fun j => rough_equal_interval_point_coordinates (a j) N (r j) (x j)
      (Fintype.mem_piFinset.mp hx j)
    choose v hv he using hcoords
    apply Finset.mem_image.mpr
    refine ⟨v, Fintype.mem_piFinset.mpr (fun j => Finset.mem_range.mpr (hv j)), ?_⟩
    funext j
    exact (he j).symm

theorem rough_equal_cube_sample_mean {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (N : ℕ) (r : κ → ℕ) (f : (κ → ℤ) → ℂ) :
    finiteComplexSetMean (roughEqualCube a N r) f =
      finiteComplexSetMean (Fintype.piFinset (fun _ : κ => Finset.range N))
        (fun v => f (fun j => roughEqualCubeOrigin a N r j+(v j : ℤ))) := by
  rw [← rough_equal_cube_sample_image]
  exact finiteComplexSetMean_image _ _ (rough_equal_cube_sample_injective a N r) f

end Hindman168
