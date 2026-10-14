import Hindman168.UnitCirclePolynomialSmallValuesCoarse
import Hindman168.ModOneNaturalMultiplier

namespace Hindman168
open Polynomial
open scoped Classical

theorem scalar_polynomial_natural_multiple_degree (p : ℝ[X]) (m D : ℕ) (hp : p.natDegree ≤ D) :
    (C (m : ℝ)*p).natDegree ≤ D := by
  have hh : (C (m : ℝ)*p).natDegree ≤ p.natDegree := by
    simpa only [natDegree_C, zero_add] using natDegree_mul_le (p := C (m : ℝ)) (q := p)
  exact hh.trans hp

/-- Actual original dense small-value points remain dense for each actual
natural polynomial multiple within its permitted real tolerance. -/
theorem scalar_polynomial_natural_multiple_small_value_density (p : ℝ[X]) (N m : ℕ)
    (δ ε γ : ℝ) (hm : (m : ℝ)*ε ≤ γ)
    (hdense : δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
      ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε)).card) :
    δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
      ‖(((C (m : ℝ)*p).eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ γ)).card := by
  have hsub : (Finset.range N).filter (fun n : ℕ =>
      ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε) ⊆
      (Finset.range N).filter (fun n : ℕ =>
        ‖(((C (m : ℝ)*p).eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ γ) := by
    intro n hn
    have hv := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨hv.1, ?_⟩
    rw [eval_mul, eval_C]
    exact (mod_one_natural_multiplier_norm_le m (p.eval (n : ℝ))).trans
      ((mul_le_mul_of_nonneg_left hv.2 (Nat.cast_nonneg m)).trans hm)
  exact hdense.trans (by exact_mod_cast Finset.card_le_card hsub)

end Hindman168
