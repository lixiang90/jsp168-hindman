import Hindman168.RoughExactInterpolation
import Mathlib.Analysis.Normed.Group.AddCircle

namespace Hindman168
open Polynomial Filter
open scoped Topology

theorem rough_mod_one_norm_eq_inf (x : ℝ) :
    ‖(x : UnitAddCircle)‖ = sInf (Set.range (fun k : ℤ => |x - (k : ℝ)|)) := by
  rw [UnitAddCircle.norm_eq]
  apply le_antisymm
  · apply le_csInf (Set.range_nonempty _)
    rintro y ⟨k, rfl⟩
    exact round_le x k
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro y ⟨k, rfl⟩
      exact abs_nonneg _
    · exact Set.mem_range_self (round x)

theorem rough_mod_one_near_integer_iff (x eps : ℝ) :
    ‖(x : UnitAddCircle)‖ ≤ eps ↔ ∃ b : ℤ, |x - (b : ℝ)| ≤ eps := by
  rw [UnitAddCircle.norm_eq]
  constructor
  · intro h
    exact ⟨round x, h⟩
  · rintro ⟨b, hb⟩
    exact (round_le x b).trans hb

theorem rough_exact_interpolation_mod_one
    {α : Type*} {l : Filter α} {W : α → ℕ} (hW : Tendsto W l atTop)
    {S Z : α → ℝ} (hg : PowerDominates l Z S)
    (hS : ∀ᶠ w in l, 1 ≤ S w) (hZ : ∀ᶠ w in l, 0 < Z w)
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
  filter_upwards [rough_exact_interpolation_eventually hW hg hS hZ e q H he heq hH A hA] with w hw
  intro t m theta hm hmsmooth hprog hrough hdeg hnorm
  apply hw t m theta hm hmsmooth hprog hrough hdeg
  intro z hz
  apply (rough_mod_one_near_integer_iff _ _).mp
  simpa only [eval_mul, eval_pow, eval_add, eval_C, eval_X, Nat.cast_add, Nat.cast_mul] using hnorm z hz

end Hindman168
