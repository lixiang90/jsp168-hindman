import Hindman168.MasterFiniteDualTemplateLimit

/-!
# Arbitrary admissible input sequences imply uniform vanishing

A stage-wise bad input is chosen whenever one exists; otherwise a known
admissible default is used. Its proved sequence limit rules out every bad
input eventually. This qualitative uniform estimate supplies no rate.
-/

namespace Hindman168

open Filter
open scoped Topology Classical

theorem uniform_zero_of_admissible_sequences {α : ℕ → Type*}
    (P : ∀ w, α w → Prop) (f : ∀ w, α w → ℝ) (base : ∀ w, α w)
    (hbase : ∀ᶠ w in atTop, P w (base w))
    (h : ∀ x : ∀ w, α w, (∀ᶠ w in atTop, P w (x w)) →
      Tendsto (fun w => f w (x w)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ x, P w x → |f w x| < ε := by
  intro ε hε
  let bad w := ∃ x : α w, P w x ∧ ε ≤ |f w x|
  let selected (w : ℕ) : α w := if hb : bad w then Classical.choose hb else base w
  have hs : ∀ᶠ w in atTop, P w (selected w) := by
    filter_upwards [hbase] with w hw
    dsimp only [selected]
    split_ifs with hb
    · exact (Classical.choose_spec hb).1
    · exact hw
  have ht := h selected hs
  have htAbs : Tendsto (fun w => |f w (selected w)|) atTop (𝓝 0) := by
    simpa only [abs_zero] using ht.abs
  filter_upwards [htAbs.eventually (Iio_mem_nhds hε)] with w hw
  intro x hx
  by_contra hn
  have hb : bad w := ⟨x, hx, le_of_not_gt hn⟩
  have hv : ε ≤ |f w (selected w)| := by
    dsimp only [selected]
    rw [dif_pos hb]
    exact (Classical.choose_spec hb).2
  exact (not_le_of_gt hw) hv

end Hindman168
