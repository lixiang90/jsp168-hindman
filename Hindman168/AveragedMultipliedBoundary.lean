import Hindman168.MultipliedBoundaryProbability
import Hindman168.FiniteConditionalLikelihood
import Mathlib.Topology.Algebra.Order.Field

/-! Boundary probabilities averaged over the original finite outside law.
Both tail products and margins may depend on all outside parameters.
The uniform bound retains that law and its exact normalization. -/

namespace Hindman168

open FiniteMass Filter
open scoped BigOperators Topology Classical

theorem rawMass_multipliedBoundary_uniform_bound {X W t H B K E : ℕ}
    (hX : 2 ≤ X) (hW : 0 < W) (ht : 0 < t) (hH : 0 < H)
    (hco : W.Coprime t) (htK : t ≤ K) (hBE : B ≤ E) (hEH : E ≤ H)
    (hlog : 2 ≤ Real.log (X : ℝ)) (hWX : (W : ℝ) / X ≤ 1) :
    event (rawMass X W) (fun p => ¬ intervalInteriorRoot H B ((t * p : ℕ) : ℤ)) ≤
      4 * (E : ℝ) / H + 12 * (W * K : ℕ) / H + (W : ℝ) * ((H : ℝ) + 1) / X := by
  have hb := rawMass_multipliedBoundary_bound hX hW ht hH hco
    (d := 1) (by simpa only [one_mul] using hBE.trans hEH) hlog hWX
  norm_num only [Nat.cast_one] at hb
  apply hb.trans
  have hbr : (B : ℝ) ≤ E := by exact_mod_cast hBE
  have htr : ((W * t : ℕ) : ℝ) ≤ (W * K : ℕ) := by exact_mod_cast Nat.mul_le_mul_left W htK
  have h1 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbr (by norm_num : (0 : ℝ) ≤ 4))
    (Nat.cast_nonneg H)
  have h2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htr (by norm_num : (0 : ℝ) ≤ 12))
    (Nat.cast_nonneg H)
  linarith

theorem joint_multipliedBoundary_bound {α : Type*} (μ : Mass α) (t B : α → ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hμt : total μ = 1) {X W H K E : ℕ}
    (hX : 2 ≤ X) (hW : 0 < W) (hH : 0 < H) (hEH : E ≤ H)
    (ht : ∀ x ∈ μ.support, 0 < t x ∧ W.Coprime (t x) ∧ t x ≤ K ∧ B x ≤ E)
    (hlog : 2 ≤ Real.log (X : ℝ)) (hWX : (W : ℝ) / X ≤ 1) :
    event (conditionalJoint μ (fun _ => rawMass X W))
      (fun xp => ¬ intervalInteriorRoot H (B xp.1) ((t xp.1 * xp.2 : ℕ) : ℤ)) ≤
      4 * (E : ℝ) / H + 12 * (W * K : ℕ) / H + (W : ℝ) * ((H : ℝ) + 1) / X := by
  rw [event_conditionalJoint]
  calc
    _ ≤ expectation μ (fun _ => 4 * (E : ℝ) / H + 12 * (W * K : ℕ) / H +
        (W : ℝ) * ((H : ℝ) + 1) / X) := by
      unfold expectation Finsupp.sum
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (rawMass_multipliedBoundary_uniform_bound hX hW
        (ht x hx).1 hH (ht x hx).2.1 (ht x hx).2.2.1 (ht x hx).2.2.2 hEH hlog hWX) (hμ x)
    _ = _ := by rw [expectation_const, hμt, one_mul]

theorem joint_multipliedBoundary_tendsto {κ α : Type*} {l : Filter κ}
    (μ : κ → Mass α) (t B : κ → α → ℕ) (X W H K E : κ → ℕ)
    (hgood : ∀ᶠ k in l, (∀ x, 0 ≤ μ k x) ∧ total (μ k) = 1 ∧
      2 ≤ X k ∧ 0 < W k ∧ 0 < H k ∧ 2 ≤ Real.log (X k : ℝ) ∧
      (W k : ℝ) / X k ≤ 1 ∧ ∀ x ∈ (μ k).support,
        0 < t k x ∧ (W k).Coprime (t k x) ∧ t k x ≤ K k ∧ B k x ≤ E k)
    (hE : Tendsto (fun k => (E k : ℝ) / H k) l (𝓝 0))
    (hK : Tendsto (fun k => ((W k * K k : ℕ) : ℝ) / H k) l (𝓝 0))
    (hend : Tendsto (fun k => (W k : ℝ) * ((H k : ℝ) + 1) / X k) l (𝓝 0)) :
    Tendsto (fun k => event (conditionalJoint (μ k) (fun _ => rawMass (X k) (W k)))
      (fun xp => ¬ intervalInteriorRoot (H k) (B k xp.1) ((t k xp.1 * xp.2 : ℕ) : ℤ))) l (𝓝 0) := by
  have hu : Tendsto (fun k => 4 * (E k : ℝ) / H k + 12 * (W k * K k : ℕ) / H k +
      (W k : ℝ) * ((H k : ℝ) + 1) / X k) l (𝓝 0) := by
    simpa only [mul_zero, zero_add, mul_div_assoc] using ((hE.const_mul 4).add (hK.const_mul 12)).add hend
  have hEH : ∀ᶠ k in l, E k ≤ H k := by
    filter_upwards [hgood, hE.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k hk he
    have hh : (0 : ℝ) < H k := by exact_mod_cast hk.2.2.2.2.1
    have he' := (div_lt_iff₀ hh).mp he
    have hr : (E k : ℝ) ≤ H k := by linarith
    exact_mod_cast hr
  apply squeeze_zero' _ _ hu
  · filter_upwards [hgood] with k hk
    obtain ⟨hμ, _, hX, hW, _, hlog, hWX, _⟩ := hk
    exact event_nonneg _ _ (conditionalJoint_nonneg _ _ hμ (fun _ _ p => by
      rw [rawMass_apply]
      exact harmonicWeight_nonneg (harmonicNormalizer_boundary_lower hX hW hlog hWX).1 p))
  · filter_upwards [hgood, hEH] with k hk he
    obtain ⟨hμ, hμt, hX, hW, hH, hlog, hWX, ht⟩ := hk
    exact joint_multipliedBoundary_bound (μ k) (t k) (B k) hμ hμt hX hW hH he ht hlog hWX

end Hindman168
