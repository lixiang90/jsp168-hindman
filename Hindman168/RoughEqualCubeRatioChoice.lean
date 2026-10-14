import Hindman168.RoughEqualCubeOriginBounds

namespace Hindman168
open scoped BigOperators Classical

theorem rough_equal_cube_small_ratio (κ : Type*) [Fintype κ]
    (c B η : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ lam ≤ c ∧
      2*B*(Fintype.card κ : ℝ)*lam/c ≤ η/4 := by
  let d : ℝ := Fintype.card κ
  let lam := min 1 (min c (η*c/(8*(B+1)*(d+1))))
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hden : 0 < 8*(B+1)*(d+1) := by positivity
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hlim : lam ≤ η*c/(8*(B+1)*(d+1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hprod := (le_div_iff₀ hden).mp hlim
  have hfactor : B*d ≤ (B+1)*(d+1) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hfactor hlam.le
  refine ⟨lam, hlam, min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  apply (div_le_iff₀ hc).mpr
  change 2*B*d*lam ≤ η/4*c
  nlinarith

end Hindman168
