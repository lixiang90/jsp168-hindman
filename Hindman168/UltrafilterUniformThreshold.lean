import Hindman168.UltrafilterBoundedDiagonal
import Mathlib.Analysis.SpecificLimits.Basic

namespace Hindman168
open Filter
open scoped Classical Topology

/-- A diagonal selection converts null testing of every selected sequence into
a positive uniform threshold. The ultrafilter must contain every tail. -/
theorem ultrafilter_uniform_null_test_threshold
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : ℕ → Type*) [∀ w, Nonempty (A w)] [∀ w, Nonempty (B w)]
    (N : ∀ w, B w → ℝ) (hN : ∀ w b, 0 ≤ N w b)
    (r : ∀ w, A w → B w → ℝ)
    (hnull : ∀ (a : ∀ w, A w) (b : ∀ w, B w),
      Tendsto (fun w => N w (b w)) (U : Filter ℕ) (𝓝 0) →
        Tendsto (fun w => r w (a w) (b w)) (U : Filter ℕ) (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ w in (U : Filter ℕ), ∀ a b, N w b ≤ δ → |r w a b| < ε := by
  intro ε hε
  by_contra hn
  let P := fun (n w : ℕ) => ∃ (a : A w) (b : B w),
    N w b ≤ 1 / ((n : ℝ) + 1) ∧ ε ≤ |r w a b|
  have hP : ∀ n, ∀ᶠ w in (U : Filter ℕ), P n w := by
    intro n
    have hnot : ¬∀ᶠ w in (U : Filter ℕ), ∀ a b,
        N w b ≤ 1 / ((n : ℝ) + 1) → |r w a b| < ε := by
      intro h
      exact hn ⟨1 / ((n : ℝ) + 1), by positivity, h⟩
    have ht := Ultrafilter.eventually_not.mpr hnot
    filter_upwards [ht] with w hw
    push Not at hw
    exact hw
  obtain ⟨stage, hstage, _, hgood⟩ := exists_slow_stage_filter (U : Filter ℕ) hU P hP
  have hc (w : ℕ) : ∃ (a : A w) (b : B w), P (stage w) w →
      N w b ≤ 1 / ((stage w : ℝ) + 1) ∧ ε ≤ |r w a b| := by
    by_cases h : P (stage w) w
    · obtain ⟨a, b, hab⟩ := h
      exact ⟨a, b, fun _ => hab⟩
    · exact ⟨Classical.choice (inferInstance : Nonempty (A w)),
        Classical.choice (inferInstance : Nonempty (B w)), fun hp => False.elim (h hp)⟩
  choose a b hab using hc
  have hsmallN : ∀ᶠ w in (U : Filter ℕ), N w (b w) ≤ 1 / ((stage w : ℝ) + 1) :=
    hgood.mono (fun w hw => (hab w hw).1)
  have hzeroN : Tendsto (fun w => N w (b w)) (U : Filter ℕ) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun w => hN w (b w))) hsmallN
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hstage)
  have hzero := (hnull a b hzeroN).abs.eventually
    (Iio_mem_nhds (by simpa only [abs_zero] using hε))
  obtain ⟨w, hw, hgoodw⟩ := (hzero.and hgood).exists
  exact (not_le_of_gt (by simpa only [abs_zero] using hw)) (hab w hgoodw).2

end Hindman168
