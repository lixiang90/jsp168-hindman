import Hindman168.SubgroupGowersRoot
import Hindman168.SubgroupCubeMomentMonotone

/-! Dimension monotonicity and control of the ambient mean for the actual
subgroup Gowers roots. No triangle inequality is assumed. -/
namespace Hindman168
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

theorem subgroupGowersValue_le_succ (d : ℕ) (hd : 0 < d) (h : G → ℝ) :
    subgroupGowersValue Q d h ≤ subgroupGowersValue Q (d + 1) h := by
  apply le_of_pow_le_pow_left₀ (pow_ne_zero (d + 1) (show (2 : ℕ) ≠ 0 by decide))
    (subgroupGowersValue_nonneg Q (d + 1) (by omega) h)
  rw [subgroupGowersValue_pow Q (d + 1) (by omega), pow_succ, pow_mul,
    subgroupGowersValue_pow Q d hd]
  exact subgroupCubeAverage_square_le_succ Q d h

theorem subgroupGowersValue_dimension_mono (d e : ℕ) (hd : 0 < d)
    (hde : d ≤ e) (h : G → ℝ) :
    subgroupGowersValue Q d h ≤ subgroupGowersValue Q e h := by
  induction e, hde using Nat.le_induction with
  | base => exact le_rfl
  | succ e hde ih =>
    exact ih.trans (subgroupGowersValue_le_succ Q e (lt_of_lt_of_le hd hde) h)

theorem subgroupCubeAverage_zero (h : G → ℝ) :
    subgroupCubeAverage Q 0 h = finiteHaarMean h := by
  have he : (default : Finset (Fin 0)) = ∅ := Subsingleton.elim _ _
  simp [subgroupCubeAverage, subgroupCubeProduct, he, finiteHaarMean_const]

theorem abs_finiteHaarMean_le_subgroupGowersValue (d : ℕ) (hd : 0 < d)
    (h : G → ℝ) : |finiteHaarMean h| ≤ subgroupGowersValue Q d h := by
  have h1 : |finiteHaarMean h| ≤ subgroupGowersValue Q 1 h := by
    apply le_of_pow_le_pow_left₀ (show (2 : ℕ) ≠ 0 by decide)
      (subgroupGowersValue_nonneg Q 1 (by decide) h)
    have hr := subgroupGowersValue_pow Q 1 (by decide) h
    norm_num only [pow_one] at hr
    rw [hr, sq_abs]
    have hm := subgroupCubeAverage_square_le_succ Q 0 h
    simpa only [subgroupCubeAverage_zero, Nat.zero_add] using hm
  exact h1.trans (subgroupGowersValue_dimension_mono Q 1 d (by decide) hd h)

end Hindman168
