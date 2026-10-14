import Hindman168.ScalarFractionalBracketAffineControl

/-! Freeze the ACTUAL linear term on a genuine complete interval block.
The original absolute slope and original N scale are retained explicitly. -/
namespace Hindman168
open scoped BigOperators

theorem scalar_fractional_bracket_block_freezing {ι : Type*} [Fintype ι]
    (β α : ℝ) (ζ γ : ι → ℝ) (a n N J : ℕ) (hN : 0 < N) (hJ : 0 < J) (hn : n < N/J)
    (B C w : ℝ) (hslope : (N : ℝ)*|α| ≤ C*w)
    (hsmall : (N : ℝ)*‖(scalarFractionalBracket β α ζ γ ((a+n : ℕ) : ℝ) : UnitAddCircle)‖ ≤ B) :
    ‖((β+α*(a : ℝ)+∑ i, ζ i*Int.fract (((a+n : ℕ) : ℝ)*γ i) : ℝ) : UnitAddCircle)‖ ≤
      B/(N : ℝ)+C*w/(J : ℝ) := by
  have hnr : (0 : ℝ) < N := by exact_mod_cast hN
  have hjr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hjn : (J : ℝ)*(n : ℝ) ≤ N := by
    have hh := (Nat.mul_le_mul_left J hn.le).trans (by
      simpa only [mul_comm] using Nat.div_mul_le_self N J)
    exact_mod_cast hh
  have hv : |α| * (n : ℝ) ≤ C*w/(J : ℝ) := by
    apply (le_div_iff₀ hjr).mpr
    have hm := mul_le_mul_of_nonneg_left hjn (abs_nonneg α)
    nlinarith
  have he : β+α*(a : ℝ)+∑ i, ζ i*Int.fract (((a+n : ℕ) : ℝ)*γ i) =
      scalarFractionalBracket β α ζ γ ((a+n : ℕ) : ℝ)-α*(n : ℝ) := by
    dsimp only [scalarFractionalBracket]
    push_cast
    ring
  have hα : ‖((α*(n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ |α| * (n : ℝ) := by
    have hh : ‖((α*(n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ |α*(n : ℝ)| :=
      (rough_mod_one_near_integer_iff _ _).mpr ⟨0,by simp⟩
    have hAbsN : |(n : ℝ)|=(n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    simpa only [abs_mul,hAbsN] using hh
  rw [he,AddCircle.coe_sub]
  exact (norm_sub_le _ _).trans (add_le_add ((le_div_iff₀' hnr).mpr hsmall) (hα.trans hv))

end Hindman168
