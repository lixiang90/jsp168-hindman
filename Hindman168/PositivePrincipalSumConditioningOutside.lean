import Hindman168.PositivePrincipalSumConditioningExposure
import Hindman168.FiniteConditionalLikelihood

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical

/-- Fine exposure exceptions of vanishing original joint mass induce an
outside exception of vanishing mass. On its complement the integrated
original kernel has coverage 1/(3Q), with no earlier-event density input. -/
theorem principal_fine_conditioning_to_outside_cover {α β γ V : Type*} [Fintype V]
    (μ : ℕ → Mass α) (ν : ℕ → α → Mass β)
    (expose : ℕ → α → β → γ) (good : ℕ → α → γ → Prop)
    (P : V → ℕ → α → β → Prop) (Q : ℕ) (hQ : 0 < Q)
    (hμ : ∀ᶠ w in atTop, ∀ x, 0 ≤ μ w x)
    (hν : ∀ᶠ w in atTop, ∀ x, (∀ y, 0 ≤ ν w x y) ∧ total (ν w x) = 1)
    (hlocal : ∀ᶠ w in atTop, ∀ x ∈ (μ w).support,
      ∀ t ∈ ((ν w x).mapDomain (expose w x)).support, good w x t →
        1 / (2 * (Q : ℝ)) ≤ ∑ v,
          event (conditionMass (ν w x) (fun y => expose w x y = t)) (P v w x))
    (hbad : Tendsto (fun w => event (conditionalJoint (μ w) (ν w))
      (fun xy => ¬ good w xy.1 (expose w xy.1 xy.2))) atTop (𝓝 0)) :
    ∃ G : ℕ → α → Prop,
      Tendsto (fun w => event (μ w) (fun x => ¬ G w x)) atTop (𝓝 0) ∧
      ∀ᶠ w in atTop, ∀ x ∈ (μ w).support, G w x →
        1 / (3 * (Q : ℝ)) ≤ ∑ v, event (ν w x) (P v w x) := by
  let bad w x := event (ν w x) (fun y => ¬ good w x (expose w x y))
  let G w x := bad w x < (1 : ℝ)/3
  have hQ' : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have he : Tendsto (fun w => expectation (μ w) (bad w)) atTop (𝓝 0) := by
    simpa only [event_conditionalJoint] using hbad
  refine ⟨G, ?_, ?_⟩
  · apply squeeze_zero' _ _ (show Tendsto (fun w => expectation (μ w) (bad w) / ((1 : ℝ)/3))
      atTop (𝓝 0) by simpa using he.div_const ((1 : ℝ)/3))
    · filter_upwards [hμ] with w hw
      exact event_nonneg _ _ hw
    · filter_upwards [hμ, hν] with w hm hn
      have h := principal_outside_markov (μ w) (bad w) hm
        (fun x => event_nonneg _ _ (hn x).1) ((1 : ℝ)/3) (by norm_num)
      simpa only [G, not_lt] using h
  · filter_upwards [hν, hlocal] with w hn hl x hx hg
    have h := principal_exposure_slot_cover (ν w x) (expose w x) (good w x)
      (fun v => P v w x) (hn x).1 (1 / (2 * (Q : ℝ))) (by positivity) (hl x hx)
    rw [(hn x).2] at h
    change _ * (1 - bad w x) ≤ _ at h
    have hc : (1 : ℝ) / (3 * Q) ≤ (1 / (2 * (Q : ℝ))) * (1 - bad w x) := by
      have hg' : bad w x < (1 : ℝ)/3 := hg
      apply (div_le_iff₀ (show 0 < 3 * (Q : ℝ) by positivity)).mpr
      field_simp
      nlinarith
    exact hc.trans h
end Hindman168
