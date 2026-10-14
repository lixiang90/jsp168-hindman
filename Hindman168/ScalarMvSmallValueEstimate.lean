import Hindman168.ScalarMvIntegerCube

namespace Hindman168
open scoped BigOperators

/-- The precise all-coefficient estimate used in degree induction. This is
only a proposition; its proof for every degree must be supplied by the induction. -/
def ScalarMvSmallValueEstimate (κ : Type*) [Fintype κ] (D : ℕ) (δ : ℝ) (B : ℕ) : Prop :=
  ∀ p : MvPolynomial κ ℝ, p.totalDegree ≤ D → ∀ N : ℕ, B ≤ N →
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ/10 →
      δ*((scalarMvIntegerCube κ N).card : ℝ) ≤
        ((scalarMvIntegerCube κ N).filter (fun x =>
          ‖((MvPolynomial.eval (fun j => (x j : ℝ)) p : ℝ) : UnitAddCircle)‖ ≤ ε)).card →
      ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ ∀ I : κ → ℕ,
        (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*MvPolynomial.coeff
          (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ)*ε

theorem scalar_mv_small_value_estimate_zero (κ : Type*) [Fintype κ]
    (δ : ℝ) (hδ : 0 < δ) : ScalarMvSmallValueEstimate κ 0 δ 1 := by
  intro p hp N hN ε _ _ hdense
  refine ⟨1, by omega, le_rfl, ?_⟩
  intro I
  simpa only [Nat.cast_one, one_mul] using scalar_mv_small_values_degree_zero p
    (by omega) N hN δ ε hδ hdense I

end Hindman168
