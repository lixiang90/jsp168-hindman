import Hindman168.ScalarMvSmallValueEstimate
import Hindman168.ScalarMvLowerDegreeLineRecovery
import Hindman168.FiniteBoundedCandidateDensity

namespace Hindman168
open scoped BigOperators Classical

/-- Select the SAME bounded multiplier on an ACTUAL dense set of directions.
The lower-degree hypothesis is explicit and every direction candidate is
constructed from its true original dense basepoint set. -/
theorem scalar_mv_common_homogeneous_directions {κ : Type*} [Fintype κ]
    (D B : ℕ) (hB : 0 < B) (μ : ℝ) (hsmall : ScalarMvSmallValueEstimate κ D μ B)
    (p : MvPolynomial κ ℝ) (hp : p.totalDegree ≤ D+1)
    (N H L c : ℕ) (hBN : B ≤ N) (hH : 0 < H) (A : ℝ) (hA : 0 ≤ A)
    (hε : A/(H : ℝ) ≤ μ/10) (s : Finset (κ → ℕ))
    (hs : s ⊆ Fintype.piFinset (fun _ : κ => Finset.range L))
    (hcount : μ*(L : ℝ)^(Fintype.card κ) ≤ s.card)
    (hrows : ∀ u ∈ s, μ*((scalarMvIntegerCube κ N).card : ℝ) ≤
      ((scalarMvIntegerCube κ N).filter (fun x => ∀ r : ℕ, 0 < r → r ≤ D+1 →
        (H : ℝ)^r*‖(((c : ℝ)*MvPolynomial.eval (fun j => (x j : ℝ))
          (scalarMvLineCoefficient p (fun j => (u j : ℝ)) r) : ℝ) : UnitAddCircle)‖ ≤ A)).card) :
    ∃ m : ℕ, 0 < m ∧ m ≤ B^(D+2) ∧ ∃ T : Finset (κ → ℕ),
      T ⊆ Fintype.piFinset (fun _ : κ => Finset.range L) ∧
      (μ/(B^(D+2) : ℕ))*(L : ℝ)^(Fintype.card κ) ≤ T.card ∧
      ∀ u ∈ T, ∀ r : ℕ, 0 < r → r ≤ D+1 →
        ‖(((m : ℝ)*((c : ℝ)*MvPolynomial.coeff 0
          (scalarMvLineCoefficient p (fun j => (u j : ℝ)) r)) : ℝ) : UnitAddCircle)‖ ≤
            (B^(D+2) : ℕ)*(A/(H : ℝ)^r) := by
  let P := B^(D+2)
  have hP : 0 < P := by dsimp only [P]; positivity
  let R := fun m : ℕ => fun u : κ → ℕ => ∀ r : ℕ, 0 < r → r ≤ D+1 →
    ‖(((m : ℝ)*((c : ℝ)*MvPolynomial.coeff 0
      (scalarMvLineCoefficient p (fun j => (u j : ℝ)) r)) : ℝ) : UnitAddCircle)‖ ≤
        (P : ℝ)*(A/(H : ℝ)^r)
  have hproduce : ∀ u ∈ s, ∃ m : ℕ, 0 < m ∧ m ≤ P ∧ R m u := by
    intro u hu
    exact scalar_mv_lower_degree_line_recovery D B hB μ hsmall p hp
      (fun j => (u j : ℝ)) N H c hBN hH A hA hε (hrows u hu)
  obtain ⟨m, hm, hmP, hdense⟩ := finite_bounded_candidate_density s P hP R hproduce
  let T := s.filter (R m)
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hT : (μ/(P : ℝ))*(L : ℝ)^(Fintype.card κ) ≤ T.card := by
    calc
      _ = (μ*(L : ℝ)^(Fintype.card κ))/(P : ℝ) := by ring
      _ ≤ (s.card : ℝ)/(P : ℝ) := div_le_div_of_nonneg_right hcount hPr.le
      _ ≤ _ := hdense
  refine ⟨m, hm, hmP, T, (Finset.filter_subset _ _).trans hs, hT, ?_⟩
  intro u hu
  exact (Finset.mem_filter.mp hu).2

end Hindman168
