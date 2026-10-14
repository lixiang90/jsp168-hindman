import Hindman168.SlowStageDiagonal
import Hindman168.FiniteSupportedEventComparison
import Mathlib.Topology.Algebra.Order.Field

/-! One supported sample sequence in prescribed positive-mass events satisfies
every fixed condition. All conditions are enumerated before later parameters
such as a sequence-selected period. No estimate at a growing index is assumed. -/
namespace Hindman168.FiniteMass
open Filter
open scoped Classical BigOperators Topology

theorem finite_event_prefix_zero_limit {α : Type*} (μ : ℕ → Mass α)
    (Bad : ℕ → ℕ → α → Prop) (hμ : ∀ᶠ w in atTop, ∀ x, 0 ≤ μ w x)
    (hBad : ∀ q, Tendsto (fun w => event (μ w) (Bad q w)) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun w => event (μ w) (fun x => ∃ q ∈ Finset.range (k+1), Bad q w x)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun w => ∑ q ∈ Finset.range (k+1), event (μ w) (Bad q w)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum (Finset.range (k+1)) (fun q _ => hBad q)
  apply tendsto_order.2
  constructor
  · intro z hz
    filter_upwards [hμ] with w hw
    exact hz.trans_le (event_nonneg _ _ hw)
  · intro z hz
    filter_upwards [hμ,hsum.eventually (gt_mem_nhds hz)] with w hw hs
    exact (event_union_bound (μ w) (Finset.range (k+1)) (fun q => Bad q w) hw).trans_lt hs

theorem countable_positive_event_diagonal {α : Type*} [Nonempty α]
    (μ : ℕ → Mass α) (Bad : ℕ → ℕ → α → Prop)
    (hμ : ∀ᶠ w in atTop, ∀ x, 0 ≤ μ w x)
    (hBad : ∀ q, Tendsto (fun w => event (μ w) (Bad q w)) atTop (𝓝 0))
    (S : ℕ → α → Prop) {β : ℝ} (hβ : 0 < β)
    (hS : ∀ᶠ w in atTop, β ≤ event (μ w) (S w))
    (P : ℕ → ℕ → Prop) (hP : ∀ k, ∀ᶠ w in atTop, P k w) :
    ∃ (stage : ℕ → ℕ) (sample : ℕ → α), Tendsto stage atTop atTop ∧
      (∀ w, stage w ≤ w) ∧
      (∀ᶠ w in atTop, sample w ∈ (μ w).support ∧ S w (sample w) ∧ P (stage w) w) ∧
      ∀ q, ∀ᶠ w in atTop, ¬ Bad q w (sample w) := by
  have hselect (k : ℕ) : ∀ᶠ w in atTop, P k w ∧
      ∃ x ∈ (μ w).support, S w x ∧ ∀ q ≤ k, ¬ Bad q w x := by
    have hfail := (finite_event_prefix_zero_limit μ Bad hμ hBad k).eventually (gt_mem_nhds hβ)
    filter_upwards [hμ,hS,hP k,hfail] with w hw hs hp hf
    refine ⟨hp,?_⟩
    by_contra hn
    have hm : event (μ w) (S w) ≤
        event (μ w) (fun x => ∃ q ∈ Finset.range (k+1), Bad q w x) := by
      apply event_mono_on_support _ _ _ hw
      intro x hx hsx
      by_contra hgood
      apply hn
      refine ⟨x,hx,hsx,?_⟩
      intro q hq hbad
      exact hgood ⟨q,Finset.mem_range.mpr (by omega),hbad⟩
    linarith
  obtain ⟨stage,htop,hsmall,hstage⟩ := exists_slow_stage _ hselect
  let quality (w : ℕ) (x : α) := x ∈ (μ w).support ∧ S w x ∧
    ∀ q ≤ stage w, ¬ Bad q w x
  let sample (w : ℕ) : α := if h : ∃ x, quality w x then Classical.choose h else Classical.choice inferInstance
  have hquality : ∀ᶠ w in atTop, quality w (sample w) := by
    filter_upwards [hstage] with w hw
    have he : ∃ x, quality w x := hw.2
    dsimp only [sample]
    rw [dif_pos he]
    exact Classical.choose_spec he
  refine ⟨stage,sample,htop,hsmall,?_,?_⟩
  · filter_upwards [hquality,hstage] with w hw hp
    exact ⟨hw.1,hw.2.1,hp.1⟩
  · intro q
    filter_upwards [hquality,htop.eventually (eventually_ge_atTop q)] with w hw hq
    exact hw.2.2 q hq

end Hindman168.FiniteMass
