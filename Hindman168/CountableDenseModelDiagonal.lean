import Hindman168.SlowStageDiagonal
import Hindman168.FiniteDenseModelSeparation
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# One bounded model sequence for countably many test classes

The finite-prefix model estimates are chosen at a proved slowly increasing
stage. The same stage can satisfy any additional countable eventual
requirements, so it can be shared with separately proved master-scale data.
-/

namespace Hindman168.FiniteMass

open Filter
open scoped Topology Classical

theorem countable_dense_model_diagonal {α : Type*}
    (μ : ℕ → Mass α) (ρ : ℕ → α → ℝ) (S : ℕ → ℕ → Set (α → ℝ))
    (P : ℕ → ℕ → Prop) (hP : ∀ q, ∀ᶠ w in atTop, P q w)
    (hmodels : ∀ q : ℕ, ∀ᶠ w in atTop, ∃ model : α → ℝ,
      (∀ x, 0 ≤ model x ∧ model x ≤ 1) ∧
      ∀ t : ℕ, t ≤ q → ∀ g ∈ S t w,
        |expectation (μ w) (fun x => (ρ w x - model x) * g x)| ≤ 1 / ((q : ℝ) + 1)) :
    ∃ (stage : ℕ → ℕ) (model : ℕ → α → ℝ), Tendsto stage atTop atTop ∧
      (∀ w, stage w ≤ w) ∧ (∀ w x, 0 ≤ model w x ∧ model w x ≤ 1) ∧
      (∀ᶠ w in atTop, P (stage w) w) ∧
      ∀ t : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop, ∀ g ∈ S t w,
        |expectation (μ w) (fun x => (ρ w x - model w x) * g x)| < η := by
  let quality (q w : ℕ) (model : α → ℝ) :=
    (∀ x, 0 ≤ model x ∧ model x ≤ 1) ∧
      ∀ t : ℕ, t ≤ q → ∀ g ∈ S t w,
        |expectation (μ w) (fun x => (ρ w x - model x) * g x)| ≤ 1 / ((q : ℝ) + 1)
  have hR (q : ℕ) : ∀ᶠ w in atTop, P q w ∧ ∃ model, quality q w model :=
    (hP q).and (hmodels q)
  obtain ⟨stage, hs, hsmall, hr⟩ := exists_slow_stage
    (fun q w => P q w ∧ ∃ model, quality q w model) hR
  let model (w : ℕ) : α → ℝ :=
    if h : ∃ model, quality (stage w) w model then Classical.choose h else 0
  have hbound (w : ℕ) (x : α) : 0 ≤ model w x ∧ model w x ≤ 1 := by
    dsimp only [model]
    split_ifs with h
    · exact (Classical.choose_spec h).1 x
    · norm_num
  have hquality : ∀ᶠ w in atTop, quality (stage w) w (model w) := by
    filter_upwards [hr] with w hw
    dsimp only [model]
    rw [dif_pos hw.2]
    exact Classical.choose_spec hw.2
  refine ⟨stage, model, hs, hsmall, hbound, hr.mono (fun _ hw => hw.1), ?_⟩
  intro t η hη
  obtain ⟨q, hq⟩ := exists_nat_one_div_lt hη
  filter_upwards [hquality, hs.eventually (eventually_ge_atTop (max t q))] with w hw hsw
  intro g hg
  have ht : t ≤ stage w := (le_max_left _ _).trans hsw
  have hqstage : q ≤ stage w := (le_max_right _ _).trans hsw
  have hrecip : 1 / ((stage w : ℝ) + 1) ≤ 1 / ((q : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.succ_le_succ hqstage
  exact ((hw.2 t ht g hg).trans hrecip).trans_lt hq

end Hindman168.FiniteMass
