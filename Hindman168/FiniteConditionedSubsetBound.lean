import Hindman168.FiniteReplicaConditioning

/-! A nonnegative statistic under a stronger good event is controlled by
its mean under the weaker event, retaining the actual normalization ratio. -/

namespace Hindman168.FiniteMass
open scoped Classical

theorem conditioned_subset_expectation_bound {α : Type*} (μ : Mass α)
    (E F : α → Prop) (hμ : ∀ x, 0 ≤ μ x) (hFE : ∀ x, F x → E x)
    (hF : 0 < event μ F) (z : α → ℝ) (hz : ∀ x, 0 ≤ z x) :
    expectation (conditionMass μ F) z ≤
      (event μ E / event μ F) * expectation (conditionMass μ E) z := by
  have hE : 0 < event μ E := hF.trans_le (event_mono μ hμ hFE)
  have hn : expectation μ (fun x => if F x then z x else 0) ≤
      expectation μ (fun x => if E x then z x else 0) := by
    apply expectation_mono _ _ _ hμ
    intro x
    by_cases hf : F x
    · simp only [if_pos hf, if_pos (hFE x hf), le_refl]
    · simp only [if_neg hf]
      split_ifs
      · exact hz x
      · exact le_rfl
  rw [expectation_conditionMass, expectation_conditionMass]
  calc
    _ ≤ expectation μ (fun x => if E x then z x else 0) / event μ F :=
      div_le_div_of_nonneg_right hn hF.le
    _ = _ := by field_simp

theorem conditioned_subset_expectation_le_twice {α : Type*} (μ : Mass α)
    (E F : α → Prop) (hμ : ∀ x, 0 ≤ μ x) (ht : total μ = 1)
    (hFE : ∀ x, F x → E x) (hF : (1 : ℝ) / 2 ≤ event μ F)
    (z : α → ℝ) (hz : ∀ x, 0 ≤ z x) :
    expectation (conditionMass μ F) z ≤ 2 * expectation (conditionMass μ E) z := by
  have hFpos : 0 < event μ F := lt_of_lt_of_le (by norm_num) hF
  have hEbound : event μ E ≤ 1 := (event_le_total μ E hμ).trans_eq ht
  have hratio : event μ E / event μ F ≤ 2 := (div_le_iff₀ hFpos).mpr (by linarith)
  exact (conditioned_subset_expectation_bound μ E F hμ hFE hFpos z hz).trans
    (mul_le_mul_of_nonneg_right hratio
      (expectation_nonneg _ _ (conditionMass_nonneg μ E hμ) hz))

end Hindman168.FiniteMass
