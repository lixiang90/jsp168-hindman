import Hindman168.UnitCircleProgressionHitCount
import Hindman168.UnitCircleDenseSmallValues

namespace Hindman168
open scoped Classical

theorem unit_circle_nat_abs_multiplier_norm (k : ℤ) (x : ℝ) :
    ‖(((k.natAbs : ℝ)*x : ℝ) : UnitAddCircle)‖ =
      ‖(((k : ℝ)*x : ℝ) : UnitAddCircle)‖ := by
  have he : (k.natAbs : ℝ) = |(k : ℝ)| := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
  rw [he]
  by_cases hk : 0 ≤ (k : ℝ)
  · rw [abs_of_nonneg hk]
  · rw [abs_of_neg (lt_of_not_ge hk), neg_mul, AddCircle.coe_neg, norm_neg]

/-- Refined recurrence from a proved coarse multiplier and actual hit count.
No interval-count inequality is assumed. The large-N threshold is explicit. -/
theorem unit_circle_refine_dense_recurrence (δ ε x b : ℝ) (hδ : 0 < δ)
    (hε : 0 ≤ ε) (hε2 : 2*ε ≤ 1) (N q A : ℕ) (hq : 0 < q)
    (hqA : q ≤ A)
    (hcoarse : (N : ℝ)*‖(((q : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ A)
    (hlarge : 8*(A : ℝ) ≤ δ*(N : ℝ))
    (hdense : δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
      ‖((b+(n : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ ε)).card) :
    (N : ℝ)*‖(((q : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ 16*(A : ℝ)*ε/δ := by
  let β := ‖(((q : ℝ)*x : ℝ) : UnitAddCircle)‖
  have hβ : 0 ≤ β := norm_nonneg _
  let s := (Finset.range N).filter (fun n : ℕ =>
    ‖((b+(n : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ ε)
  have hb := unit_circle_progression_hit_count s N q hq (Finset.filter_subset _ _)
    x b ε hε hε2 (by
      have h := abs_sub_round ((q : ℝ)*x)
      linarith) (fun n hn => (Finset.mem_filter.mp hn).2)
  rw [← UnitAddCircle.norm_eq] at hb
  change β*(s.card : ℝ) ≤ (β*(N : ℝ)+3*(q : ℝ))*(β+2*ε) at hb
  have hd := mul_le_mul_of_nonneg_left hdense hβ
  have hqAr : (q : ℝ) ≤ A := by exact_mod_cast hqA
  have hfactor : β*(N : ℝ)+3*(q : ℝ) ≤ 4*(A : ℝ) := by
    change (N : ℝ)*β ≤ A at hcoarse
    nlinarith
  have hc := mul_le_mul_of_nonneg_right hfactor (by positivity : 0 ≤ β+2*ε)
  have ht := mul_le_mul_of_nonneg_right hlarge hβ
  change β*(δ*(N : ℝ)) ≤ β*(s.card : ℝ) at hd
  apply (le_div_iff₀ hδ).mpr
  change (N : ℝ)*β*δ ≤ _
  nlinarith

/-- Genuine strong scalar linear recurrence on sufficiently long intervals.
One bound depends only on delta; all coefficients and epsilon are arbitrary. -/
theorem unit_circle_strong_linear_recurrence (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ (x b : ℝ) (N : ℕ), 0 < N → ∀ ε : ℝ,
      0 ≤ ε → ε ≤ δ/10 → 8*(A : ℝ) ≤ δ*(N : ℝ) →
      δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
        ‖((b+(n : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ ε)).card →
      ∃ q : ℕ, 0 < q ∧ q ≤ A ∧
        (N : ℝ)*‖(((q : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ 16*(A : ℝ)*ε/δ := by
  obtain ⟨A, hA, hinv⟩ := unit_circle_dense_small_values_coarse_inverse δ hδ hδ1
  refine ⟨A, hA, ?_⟩
  intro x b N hN ε hε hεsmall hlarge hdense
  obtain ⟨k, hk, hkA, hkcoarse⟩ := hinv x b N hN ε hεsmall hdense
  have hcoarse : (N : ℝ)*‖(((k.natAbs : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ A := by
    rwa [unit_circle_nat_abs_multiplier_norm]
  refine ⟨k.natAbs, hk, hkA, ?_⟩
  exact unit_circle_refine_dense_recurrence δ ε x b hδ hε (by linarith) N k.natAbs A
    hk hkA hcoarse hlarge hdense

end Hindman168
