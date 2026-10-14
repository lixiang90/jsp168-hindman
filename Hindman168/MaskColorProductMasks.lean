import Hindman168.MaskBoundedCountSampling

/-! The complete product-color mask includes every nonempty subset,
including singleton subsets, with the actual natural master coefficients. -/

namespace Hindman168
open scoped BigOperators Classical

noncomputable def maskColorProductMask {m N r : ℕ} (a : Fin (m+1) → ℚ)
    (C : ℕ → Chain (m+1)) (χ : ℕ → Fin r) (color : Fin r) (w : ℕ)
    (V : Finset (Fin (m+1))) (y : ℤ) : ℝ :=
  if 0 < y ∧ χ ((∏ k ∈ V, masterColumnCoefficient N a (fun w => (C w).block) w k) * y.toNat) = color
    then 1 else 0

theorem maskColorProductMask_unit {m N r : ℕ} (a : Fin (m+1) → ℚ)
    (C : ℕ → Chain (m+1)) (χ : ℕ → Fin r) (color : Fin r) (w : ℕ)
    (V : Finset (Fin (m+1))) (y : ℤ) :
    0 ≤ maskColorProductMask (N := N) a C χ color w V y ∧
      |maskColorProductMask (N := N) a C χ color w V y| ≤ 1 := by
  unfold maskColorProductMask
  split_ifs <;> norm_num

theorem maskColorProductMask_natural {m N r : ℕ} (a : Fin (m+1) → ℚ)
    (C : ℕ → Chain (m+1)) (χ : ℕ → Fin r) (color : Fin r) (w : ℕ)
    (V : Finset (Fin (m+1))) (z : Fin (m+1) → ℕ) (hz : ∀ k ∈ V, 0 < z k) :
    maskColorProductMask (N := N) a C χ color w V ((∏ k ∈ V, z k : ℕ) : ℤ) =
      if χ (∏ k ∈ V, masterColumnCoefficient N a (fun w => (C w).block) w k * z k) = color
        then 1 else 0 := by
  have hp : 0 < ∏ k ∈ V, z k := Finset.prod_pos hz
  simp only [maskColorProductMask, Int.natCast_pos.mpr hp, true_and, Int.toNat_natCast,
    ← Finset.prod_mul_distrib]

end Hindman168
