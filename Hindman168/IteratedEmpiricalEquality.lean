import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

/-! Length-first local approximation plus actual empirical comparison forces
identical limiting readings, without any diagonal choice alpha(m). -/
namespace Hindman168
open Filter
open scoped Topology

theorem iterated_empirical_limits_equal (a b : ℝ → ℕ → ℂ) (A B : ℂ)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ α : ℝ, 0 < α → α < r →
      ∀ᶠ m in atTop, ‖a α m-A‖ < ε)
    (hb : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ α : ℝ, 0 < α → α < r →
      ∀ᶠ m in atTop, ‖b α m-B‖ < ε)
    (hcompare : ∀ α : ℝ, 0 < α → Tendsto (fun m => a α m-b α m) atTop (𝓝 0)) : A = B := by
  by_contra hne
  have hpos : 0 < ‖A-B‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have he : 0 < ‖A-B‖/4 := by positivity
  obtain ⟨ra,hra,hra'⟩ := ha _ he
  obtain ⟨rb,hrb,hrb'⟩ := hb _ he
  let α := min ra rb/2
  have hα : 0 < α := half_pos (lt_min hra hrb)
  have har : α < ra := (half_lt_self (lt_min hra hrb)).trans_le (min_le_left _ _)
  have hbr : α < rb := (half_lt_self (lt_min hra hrb)).trans_le (min_le_right _ _)
  have hc := Metric.tendsto_nhds.mp (hcompare α hα) _ he
  have hall := (hra' α hα har).and ((hrb' α hα hbr).and hc)
  obtain ⟨m,ham,hbm,hcm⟩ := hall.exists
  simp only [dist_zero_right] at hcm
  have hid : A-B = (A-a α m)+(a α m-b α m)+(b α m-B) := by ring
  have ht : ‖A-B‖ ≤ ‖a α m-A‖+‖a α m-b α m‖+‖b α m-B‖ := by
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add (by simpa only [norm_sub_rev] using norm_add_le (A-a α m) (a α m-b α m)) le_rfl)
  linarith

end Hindman168
