import Hindman168.UnitTorusFiniteDiscrepancy

namespace Hindman168
open scoped BigOperators Classical Topology

/-- Actual nonzero integer-vector mode selection. Accuracy and character
l1 size bound precede EVERY sample set, torus orbit and unit Lipschitz observable. -/
theorem unit_torus_finite_observable_phase_selection (κ : Type*) [Fintype κ]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ K : ℕ, 0 < K ∧
      ∀ {α : Type*} (s : Finset α), s.Nonempty → ∀ f : α → UnitAddTorus κ,
        ∀ F ∈ unitLipschitzObservables (UnitAddTorus κ),
          δ ≤ ‖unitTorusFiniteDiscrepancy s f F‖ →
          ∃ k : κ → ℤ, k ≠ 0 ∧ (∑ j, (k j).natAbs) ≤ K ∧
            η ≤ ‖finiteComplexSetMean s (fun a => UnitAddTorus.mFourier k (f a))‖ := by
  obtain ⟨P, hP⟩ := unit_torus_finite_uniform_fourier_family κ (δ/8) (by positivity)
  let B : ℝ := 1+∑ c ∈ P, ∑ k ∈ c.support, ‖c k‖
  let K : ℕ := 1+∑ c ∈ P, ∑ k ∈ c.support, ∑ j, (k j).natAbs
  let η := min (δ/(4*B)) (1/2)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hK : 0 < K := by dsimp only [K]; omega
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hbudget : ∀ c ∈ P, ∑ k ∈ c.support, ‖c k‖ ≤ B := by
    intro c hc
    have hh : (∑ k ∈ c.support, ‖c k‖) ≤ ∑ a ∈ P, ∑ k ∈ a.support, ‖a k‖ :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun k _ => norm_nonneg (a k))) hc
    dsimp only [B]
    linarith only [hh]
  have hfreq : ∀ c ∈ P, ∀ k ∈ c.support, (∑ j, (k j).natAbs) ≤ K := by
    intro c hc k hk
    have h1 : (∑ j, (k j).natAbs) ≤ ∑ t ∈ c.support, ∑ j, (t j).natAbs :=
      Finset.single_le_sum (f := fun t : κ → ℤ => ∑ j, (t j).natAbs)
        (fun t _ => Nat.zero_le _) hk
    have h2 : (∑ t ∈ c.support, ∑ j, (t j).natAbs) ≤
        ∑ a ∈ P, ∑ t ∈ a.support, ∑ j, (t j).natAbs :=
      Finset.single_le_sum (f := fun a : (κ → ℤ) →₀ ℂ => ∑ t ∈ a.support, ∑ j, (t j).natAbs)
        (fun a _ => Nat.zero_le _) hc
    dsimp only [K]
    omega
  refine ⟨η, hη, hη1, K, hK, ?_⟩
  intro α s hs f F hF hbad
  obtain ⟨c, hc, happrox⟩ := hP F hF
  let G : C(UnitAddTorus κ, ℂ) := c.sum (fun k a => a •
    (UnitAddTorus.mFourier k : C(UnitAddTorus κ, ℂ)))
  have htriangle : ‖unitTorusFiniteDiscrepancy s f F‖ ≤
      ‖unitTorusFiniteDiscrepancy s f G‖+2*‖F-G‖ := by
    calc
      _ = ‖unitTorusFiniteDiscrepancy s f G+unitTorusFiniteDiscrepancy s f (F-G)‖ := by
        rw [map_sub]
        congr 1
        abel
      _ ≤ ‖unitTorusFiniteDiscrepancy s f G‖+‖unitTorusFiniteDiscrepancy s f (F-G)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (unit_torus_finite_discrepancy_norm_bound s f (F-G))
  have hlarge : δ/2 ≤ ‖unitTorusFiniteDiscrepancy s f G‖ := by
    change ‖F-G‖ < δ/8 at happrox
    linarith only [hbad, htriangle, happrox, hδ]
  obtain ⟨k, hk, hk0, hkmean⟩ := unit_torus_finite_fourier_large_frequency s hs f c B δ
    hB hδ (hbudget c hc) hlarge
  rw [unit_torus_finite_nonzero_fourier_discrepancy s f k hk0] at hkmean
  exact ⟨k, hk0, hfreq c hc k hk, (min_le_left _ _).trans hkmean⟩

end Hindman168
