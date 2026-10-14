import Hindman168.ScalarMvSmallValuesCoarse
import Hindman168.ModOneNaturalMultiplier

namespace Hindman168
open scoped Classical

theorem scalar_mv_natural_multiple_degree {κ : Type*}
    (p : MvPolynomial κ ℝ) (m D : ℕ) (hp : p.totalDegree ≤ D) :
    (MvPolynomial.C (m : ℝ)*p).totalDegree ≤ D :=
  (MvPolynomial.totalDegree_mul _ _).trans (by simpa only [MvPolynomial.totalDegree_C, zero_add] using hp)

/-- Every permitted ACTUAL natural multiple retains the original actual
dense samples, without changing the cube or its distribution. -/
theorem scalar_mv_natural_multiple_small_value_density {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (N m : ℕ) (δ ε γ : ℝ) (hm : (m : ℝ)*ε ≤ γ)
    (hdense : δ*((scalarMvIntegerCube κ N).card : ℝ) ≤
      ((scalarMvIntegerCube κ N).filter (fun x => ‖scalarMvCircleOrbit p x‖ ≤ ε)).card) :
    δ*((scalarMvIntegerCube κ N).card : ℝ) ≤
      ((scalarMvIntegerCube κ N).filter (fun x =>
        ‖scalarMvCircleOrbit (MvPolynomial.C (m : ℝ)*p) x‖ ≤ γ)).card := by
  have hsub : ((scalarMvIntegerCube κ N).filter (fun x => ‖scalarMvCircleOrbit p x‖ ≤ ε)) ⊆
      (scalarMvIntegerCube κ N).filter (fun x =>
        ‖scalarMvCircleOrbit (MvPolynomial.C (m : ℝ)*p) x‖ ≤ γ) := by
    intro x hx
    have hv := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hv.1, ?_⟩
    rw [scalarMvCircleOrbit, map_mul, MvPolynomial.eval_C]
    exact (mod_one_natural_multiplier_norm_le m _).trans
      ((mul_le_mul_of_nonneg_left hv.2 (Nat.cast_nonneg m)).trans hm)
  exact hdense.trans (by exact_mod_cast Finset.card_le_card hsub)

end Hindman168
