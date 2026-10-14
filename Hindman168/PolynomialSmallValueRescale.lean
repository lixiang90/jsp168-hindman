import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hindman168

/-- Clear genuine positive denominators in the multiplier-index recurrence.
The actual lower bound on its length produces the desired original epsilon. -/
theorem polynomial_small_value_recurrence_rescale (δ μ ε L X β K B : ℝ)
    (hδ : 0 < δ) (hμ : 0 < μ) (hε : 0 < ε) (hX : 0 < X) (hβ : 0 ≤ β)
    (hL : δ/(20*ε) ≤ L) (hrec : L*β ≤ 16*K*(B/X)/μ) :
    X*β ≤ (320*K*B/(μ*δ))*ε := by
  have hden := (le_div_iff₀ hμ).mp hrec
  have hmul := mul_le_mul_of_nonneg_right hden hX.le
  have he : (16*K*(B/X))*X = 16*K*B := by field_simp
  rw [he] at hmul
  have hlow := (div_le_iff₀ (by positivity : 0 < 20*ε)).mp hL
  have hlowmul := mul_le_mul_of_nonneg_right hlow (mul_nonneg (mul_nonneg hX.le hβ) hμ.le)
  have hupper := mul_le_mul_of_nonneg_right hmul hε.le
  have hr : X*β ≤ 320*K*B*ε/(μ*δ) := by
    apply (le_div_iff₀ (mul_pos hμ hδ)).mpr
    nlinarith only [hlowmul, hupper]
  have heq : 320*K*B*ε/(μ*δ) = (320*K*B/(μ*δ))*ε := by ring
  rwa [heq] at hr

end Hindman168
