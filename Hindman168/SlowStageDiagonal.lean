import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Finset.Max

/-!
# A slowly increasing stage for countably many eventual requirements

Each fixed requirement has a proved eventual threshold. The selected stage
is the largest index at most w whose threshold has been reached. It tends
to infinity and satisfies its own requirement eventually; no uniform rate
or estimate at an arbitrary growing index is assumed.
-/

namespace Hindman168

open Filter
open scoped Classical

theorem exists_slow_stage (R : ℕ → ℕ → Prop)
    (hR : ∀ q, ∀ᶠ w in atTop, R q w) :
    ∃ stage : ℕ → ℕ, Tendsto stage atTop atTop ∧
      (∀ w, stage w ≤ w) ∧ ∀ᶠ w in atTop, R (stage w) w := by
  have thresholds (q : ℕ) : ∃ t : ℕ, ∀ w, t ≤ w → R q w :=
    eventually_atTop.mp (hR q)
  choose threshold hthreshold using thresholds
  let good (w : ℕ) := (Finset.range (w + 1)).filter (fun q => threshold q ≤ w)
  let stage (w : ℕ) := if hn : (good w).Nonempty then (good w).max' hn else 0
  have hmem {q w : ℕ} (hq : q ≤ w) (ht : threshold q ≤ w) : q ∈ good w :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ht⟩
  have hstage (w : ℕ) : stage w ≤ w := by
    dsimp only [stage]
    split_ifs with hn
    · have h := (Finset.mem_filter.mp ((good w).max'_mem hn)).1
      exact Nat.le_of_lt_succ (Finset.mem_range.mp h)
    · exact Nat.zero_le _
  have htendsto : Tendsto stage atTop atTop := by
    apply tendsto_atTop.mpr
    intro q
    filter_upwards [eventually_ge_atTop (max q (threshold q))] with w hw
    have hqmem := hmem ((le_max_left _ _).trans hw) ((le_max_right _ _).trans hw)
    have hn : (good w).Nonempty := ⟨q, hqmem⟩
    dsimp only [stage]
    rw [dif_pos hn]
    exact (good w).le_max' q hqmem
  have hr : ∀ᶠ w in atTop, R (stage w) w := by
    filter_upwards [eventually_ge_atTop (threshold 0)] with w hw
    have hn : (good w).Nonempty := ⟨0, hmem (Nat.zero_le _) hw⟩
    apply hthreshold (stage w) w
    dsimp only [stage]
    rw [dif_pos hn]
    exact (Finset.mem_filter.mp ((good w).max'_mem hn)).2
  exact ⟨stage, htendsto, hstage, hr⟩

end Hindman168
