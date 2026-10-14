import Hindman168.NativeSubgroupLevelCharacters
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual character escape is retained under a positive lower comparison
of real scales, including passage to the natural floor of a cofinal scale.
All comparisons occur outside the circle norm. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_subgroup_irrational_scale_comparison {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L K : ℕ → ℝ) (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hIrr : NativeSubgroupSequentialIrrational D F L p)
    (c : ℝ) (hc : 0 < c)
    (hCompare : ∀ᶠ n in atTop, 0 ≤ L n ∧ c*L n ≤ K n) :
    NativeSubgroupSequentialIrrational D F K p := by
  intro j hj hjTop phi hphi
  have h := (hIrr j hj hjTop phi hphi).const_mul_atTop (pow_pos hc j)
  apply tendsto_atTop_mono' _ _ h
  filter_upwards [hCompare] with n hn
  rw [← mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (mul_nonneg hc.le hn.1) hn.2 j) (norm_nonneg _)

theorem native_subgroup_irrational_nat_floor {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hIrr : NativeSubgroupSequentialIrrational D F L p) :
    NativeSubgroupSequentialIrrational D F (fun n => (⌊L n⌋₊ : ℝ)) p := by
  apply native_subgroup_irrational_scale_comparison D F L _ p hIrr (1/2) (by norm_num)
  filter_upwards [hL.eventually_ge_atTop 2] with n hn
  have hf := Nat.sub_one_lt_floor (L n)
  constructor <;> linarith

end Hindman168
