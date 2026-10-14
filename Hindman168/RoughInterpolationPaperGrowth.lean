import Hindman168.RoughExactInterpolationModOne

namespace Hindman168
open Polynomial Filter Asymptotics
open scoped Topology

theorem rough_interpolation_growth_from_ratios
    {α : Type*} {l : Filter α} {S Z : α → ℝ}
    (hS : Tendsto S l atTop)
    (hr : ∀ n : ℕ, 0 < n → Tendsto (fun w => Z w / S w ^ n) l atTop) :
    PowerDominates l Z S ∧ (∀ᶠ w in l, 1 ≤ S w) ∧ (∀ᶠ w in l, 0 < Z w) := by
  have hSone := hS.eventually (eventually_ge_atTop (1 : ℝ))
  have hZ : ∀ᶠ w in l, 0 < Z w := by
    filter_upwards [hSone, (hr 1 (by omega)).eventually (eventually_gt_atTop (0 : ℝ))]
      with w hSw hrw
    simpa only [pow_one] using (div_pos_iff.mp hrw).resolve_right (by intro h; linarith [h.2]) |>.1
  refine ⟨?_, hSone, hZ⟩
  intro n
  have hn : (fun w => S w ^ (n + 1)) =o[l] Z := by
    apply (isLittleO_iff_tendsto' ?_).mpr
    · have hi : Tendsto (fun w => (Z w / S w ^ (n + 1))⁻¹) l (𝓝 0) :=
        (hr (n + 1) (by omega)).inv_tendsto_atTop
      simpa only [inv_div] using hi
    · filter_upwards [hZ] with w hw hz
      exact (hw.ne' hz).elim
  apply IsBigO.trans_isLittleO (g := fun w => S w ^ (n + 1)) _ hn
  apply IsBigO.of_bound 1
  filter_upwards [hSone] with w hw
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ S w) _), one_mul]
  rw [pow_succ]
  exact le_mul_of_one_le_right (pow_nonneg (by linarith) _) hw

theorem rough_exact_interpolation_paper
    {α : Type*} {l : Filter α} {W : α → ℕ} (hW : Tendsto W l atTop)
    {S Z : α → ℝ} (hS : Tendsto S l atTop)
    (hr : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w / (S w) ^ a) l atTop)
    (e q H : ℕ) (he : 0 < e) (heq : e ≤ q) (hH : 2 * q + 2 ≤ H)
    (A : ℝ) (hA : 0 < A) :
    ∀ᶠ w in l, ∀ (t m : ℕ) (theta : ℝ[X]), 0 < m →
      (∀ p, p.Prime → p ∣ m → p ≤ W w) →
      (∀ z : ℕ, z < H → S w ≤ (t + m * z : ℕ) ∧ (t + m * z : ℕ) < 2 * S w) →
      (∀ z : ℕ, z < H → (primorial (W w)).Coprime (t + m * z)) →
      ((C (t : ℝ) + C (m : ℝ) * X) ^ e * theta).natDegree ≤ q →
      (∀ z : ℕ, z < H →
        ‖((((t + m * z : ℕ) : ℝ) ^ e * theta.eval (z : ℝ) : ℝ) : UnitAddCircle)‖ ≤
          A * (S w / Z w) ^ e) →
      ∃ M : ℚ[X], M.natDegree ≤ q - e ∧
        (∀ j p, p.Prime → p ∣ (M.coeff j).den → p ≤ W w) ∧
        ∀ z : ℕ, z < H → (∃ b : ℤ, M.eval (z : ℚ) = b) ∧
          |theta.eval (z : ℝ) - ((M.eval (z : ℚ) : ℚ) : ℝ)| ≤
            roughInterpolationConstant q * A * (Z w)⁻¹ ^ e := by
  have hn : ∀ n : ℕ, 0 < n → Tendsto (fun w => Z w / S w ^ n) l atTop := by
    intro n hn
    simpa only [Real.rpow_natCast] using hr (n : ℝ) (by exact_mod_cast hn)
  obtain ⟨hg, hSone, hZ⟩ := rough_interpolation_growth_from_ratios hS hn
  exact rough_exact_interpolation_mod_one hW hg hSone hZ e q H he heq hH A hA

end Hindman168
