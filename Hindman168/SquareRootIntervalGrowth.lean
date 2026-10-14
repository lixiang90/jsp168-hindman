import Hindman168.PowerGrowth
import Mathlib.Data.Nat.Sqrt

/-!
# Concrete square-root auxiliary intervals

The integer square root of an original interval length still dominates
all fixed powers of the budget. Its relative translation loss is rapidly
small. These facts are derived from length growth, rather than assuming
that the desired insertion error tends to zero.
-/

namespace Hindman168

open Filter Asymptotics
open scoped Topology

theorem nat_sqrt_quadratic_bounds {T : ℕ} (hT : 0 < T) :
    1 ≤ Nat.sqrt T ∧ (Nat.sqrt T : ℝ) ^ 2 ≤ T ∧
      (T : ℝ) ≤ 4 * (Nat.sqrt T : ℝ) ^ 2 := by
  have hL : 1 ≤ Nat.sqrt T := Nat.sqrt_pos.mpr hT
  have hsq : (Nat.sqrt T : ℝ) ^ 2 ≤ T := by exact_mod_cast Nat.sqrt_le' T
  have hu : (T : ℝ) < ((Nat.sqrt T : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' T
  have hLr : (1 : ℝ) ≤ Nat.sqrt T := by exact_mod_cast hL
  exact ⟨hL, hsq, by nlinarith⟩

theorem PowerDominates.nat_sqrt {α : Type*} {l : Filter α}
    {T : α → ℕ} {Q : α → ℝ}
    (hD : PowerDominates l (fun w => (T w : ℝ)) Q)
    (hQ : ∀ᶠ w in l, 0 ≤ Q w) :
    PowerDominates l (fun w => (Nat.sqrt (T w) : ℝ)) Q := by
  have hT : ∀ᶠ w in l, 0 < T w := by
    filter_upwards [(hD 0).bound (by norm_num : (0 : ℝ) < 1)] with w hw
    simp only [pow_zero, Real.norm_eq_abs, abs_one,
      abs_of_nonneg (Nat.cast_nonneg (T w) : (0 : ℝ) ≤ T w), one_mul] at hw
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hw)
  intro n
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [(hD (2 * n)).bound (by positivity : (0 : ℝ) < c ^ 2 / 4), hT, hQ]
    with w hw hTw hQw
  have hL := nat_sqrt_quadratic_bounds hTw
  have hLn : (0 : ℝ) ≤ Nat.sqrt (T w) := Nat.cast_nonneg _
  have hn : 0 ≤ Q w ^ n := pow_nonneg hQw n
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hQw _),
    abs_of_nonneg (Nat.cast_nonneg (T w) : (0 : ℝ) ≤ T w)] at hw
  rw [mul_comm 2 n, pow_mul] at hw
  simp only [Real.norm_eq_abs, abs_of_nonneg hn, abs_of_nonneg hLn]
  have hs : (Q w ^ n) ^ 2 ≤ (c * (Nat.sqrt (T w) : ℝ)) ^ 2 := by
    calc
      _ ≤ c ^ 2 / 4 * (T w : ℝ) := hw
      _ ≤ c ^ 2 / 4 * (4 * (Nat.sqrt (T w) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hL.2.2 (by positivity)
      _ = _ := by ring
  exact (sq_le_sq₀ hn (mul_nonneg hc.le hLn)).mp hs

theorem nat_sqrt_relative_loss {T : ℕ} (hT : 0 < T) :
    2 * (Nat.sqrt T : ℝ) / T ≤ 2 / (Nat.sqrt T : ℝ) := by
  have hL : (0 : ℝ) < Nat.sqrt T := by exact_mod_cast Nat.sqrt_pos.mpr hT
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  rw [div_le_div_iff₀ hTr hL]
  nlinarith [(nat_sqrt_quadratic_bounds hT).2.1]

theorem nat_sqrt_translation_loss_rapid {α : Type*} {l : Filter α}
    {T : α → ℕ} {Q V : α → ℝ}
    (hD : PowerDominates l (fun w => (T w : ℝ)) Q)
    (hVQ : ∀ᶠ w in l, 1 ≤ V w ∧ V w ≤ Q w) :
    RapidlySmall l V (fun w => 2 * (Nat.sqrt (T w) : ℝ) / T w) := by
  have hQ := hVQ.mono (fun _ hw => zero_le_one.trans (hw.1.trans hw.2))
  have hL := hD.nat_sqrt hQ
  have hLp : ∀ᶠ w in l, 0 < Nat.sqrt (T w) := by
    filter_upwards [(hL 0).bound (by norm_num : (0 : ℝ) < 1)] with w hw
    simp only [pow_zero, Real.norm_eq_abs, abs_one,
      abs_of_nonneg (Nat.cast_nonneg (Nat.sqrt (T w)) : (0 : ℝ) ≤ Nat.sqrt (T w)), one_mul] at hw
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hw)
  apply rapid_of_polynomial_majorant hL
    (hLp.mono (fun _ hw => by exact_mod_cast hw)) hVQ 0 (by norm_num : (0 : ℝ) < 2)
  filter_upwards [hLp] with w hw
  have hT := Nat.sqrt_pos.mp hw
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (Nat.sqrt (T w) : ℝ) / T w),
    pow_zero, mul_one]
  exact nat_sqrt_relative_loss hT

end Hindman168
