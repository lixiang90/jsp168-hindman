import Hindman168.AlignmentBadMassCompactness
import Mathlib.Data.ENNReal.Inv

/-! The ordinary-filter contradiction in the native probability codomain.
A selected good subsequence must be obtained from EVERY cofinal positive
failure event. No interchange of real-valued liminf and toReal is needed. -/
namespace Hindman168
open Filter FiniteMass
open scoped Topology ENNReal

theorem selected_alignment_failure_mass_zero_of_compactness {α : Type*}
    (μ : ℕ → Mass α) (p : ℕ → α → ℝ≥0∞) (c C : ℝ≥0∞) (hcC : c < C)
    (hμ : ∀ᶠ w in atTop, ∀ x, 0 ≤ μ w x)
    (hcompact : ∀ W : ℕ → ℕ, Tendsto W atTop atTop → ∀ β : ℝ, 0 < β →
      (∀ᶠ m in atTop, β ≤ event (μ (W m)) (fun x => p (W m) x < c)) →
      ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ sample : ℕ → α,
        (∀ᶠ m in atTop, p (W (f m)) (sample m) < c) ∧
        C ≤ atTop.liminf (fun m => p (W (f m)) (sample m))) :
    Tendsto (fun w => event (μ w) (fun x => p w x < c)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hμ] with w hw
    exact ha.trans_le (event_nonneg _ _ hw)
  · intro β hβ
    by_contra hn
    have hfreq : ∃ᶠ w in atTop, β ≤ event (μ w) (fun x => p w x < c) := by
      change ¬ ∀ᶠ w in atTop, ¬ β ≤ event (μ w) (fun x => p w x < c)
      simpa only [not_le] using hn
    obtain ⟨W,hW,_,hbad⟩ := rough_cofinal_frequent_strict_subsequence id tendsto_id
      (fun w => β ≤ event (μ w) (fun x => p w x < c)) hfreq
    obtain ⟨f,hf,sample,hfail,hlim⟩ := hcompact W hW.tendsto_atTop β hβ
      (Eventually.of_forall hbad)
    have hu := liminf_le_of_frequently_le (hfail.mono (fun _ h => h.le)).frequently
    exact (not_le_of_gt hcC) (hlim.trans hu)

end Hindman168
