import Hindman168.QuotientIntervalGrowth
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semifield

/-! Exact floor identification and all-power growth of the paper's
modulus-aligned square-root microcell and its progression length. -/

namespace Hindman168

open Filter
open scoped Topology

def alignedSqrtMicrocellWidth (H M : ℕ) : ℕ := M * (Nat.sqrt H / M)

theorem alignedSqrtMicrocellWidth_floor (H M : ℕ) :
    alignedSqrtMicrocellWidth H M = M * ⌊Real.sqrt (H : ℝ) / M⌋₊ := by
  rw [Nat.floor_div_natCast, Real.nat_floor_real_sqrt_eq_nat_sqrt]
  rfl

theorem alignedSqrtMicrocellWidth_div {H M : ℕ} (hM : 0 < M) :
    alignedSqrtMicrocellWidth H M / M = Nat.sqrt H / M := by
  exact Nat.mul_div_right _ hM

theorem alignedSqrtMicrocellWidth_growth {κ : Type*} {l : Filter κ}
    (H M : κ → ℕ) (Q : κ → ℝ)
    (hH : PowerDominates l (fun k => (H k : ℝ)) Q) (p : ℕ)
    (hQ : ∀ᶠ k in l, 2 ≤ Q k)
    (hM : ∀ᶠ k in l, 0 < M k ∧ (M k : ℝ) ≤ Q k ^ p) :
    PowerDominates l (fun k => (alignedSqrtMicrocellWidth (H k) (M k) : ℝ)) Q := by
  have hn := (hH.nat_sqrt (hQ.mono (fun _ hk => zero_le_two.trans hk))).nat_div p hQ hM
  apply hn.mono_right
  filter_upwards [hM] with k hk
  refine ⟨Nat.cast_nonneg _, ?_⟩
  exact_mod_cast Nat.le_mul_of_pos_left (Nat.sqrt (H k) / M k) hk.1

theorem alignedSqrtMicrocellLength_growth {κ : Type*} {l : Filter κ}
    (H M : κ → ℕ) (Q : κ → ℝ)
    (hH : PowerDominates l (fun k => (H k : ℝ)) Q) (p : ℕ)
    (hQ : ∀ᶠ k in l, 2 ≤ Q k)
    (hM : ∀ᶠ k in l, 0 < M k ∧ (M k : ℝ) ≤ Q k ^ p) :
    PowerDominates l (fun k => (Nat.sqrt (H k) / M k : ℕ)) Q :=
  (hH.nat_sqrt (hQ.mono (fun _ hk => zero_le_two.trans hk))).nat_div p hQ hM

end Hindman168
