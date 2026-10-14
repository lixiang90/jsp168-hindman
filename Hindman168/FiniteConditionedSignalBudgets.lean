import Hindman168.FinitePositiveThresholdMinimum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! ACTUAL finite GOOD subset receives one true positive signal threshold
and one natural budget. Invalid members and the empty finite pool are
handled explicitly; no false geometry is assigned to them. -/
namespace Hindman168
open scoped Classical BigOperators

theorem finite_conditioned_signal_budgets {ι : Type*} [Fintype ι]
    (Good : ι → Prop) (P : ι → ℕ → ℝ → Prop)
    (hP : ∀ i, Good i → ∃ n : ℕ, 0 < n ∧ ∃ r : ℝ, 0 < r ∧ P i n r) :
    ∃ B : ℕ, 0 < B ∧ ∃ θ : ℝ, 0 < θ ∧ ∀ i, Good i →
      ∃ n : ℕ, 0 < n ∧ n ≤ B ∧ ∃ r : ℝ, 0 < r ∧ θ ≤ r ∧ P i n r := by
  have hEach (i : ι) : ∃ n : ℕ, 0 < n ∧ ∃ r : ℝ, 0 < r ∧ (Good i → P i n r) := by
    by_cases hi : Good i
    · obtain ⟨n,hn,r,hr,h⟩ := hP i hi
      exact ⟨n,hn,r,hr,fun _ => h⟩
    · exact ⟨1,by omega,1,by norm_num,fun h => (hi h).elim⟩
  choose n hn r hr hData using hEach
  let B := 1+∑ i, n i
  have hB : 0 < B := by dsimp only [B]; omega
  have hNB (i : ι) : n i ≤ B :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (by dsimp only [B]; omega)
  by_cases hI : Nonempty ι
  · letI := hI
    obtain ⟨θ,hθ,hLe⟩ := finite_positive_threshold_minimum r hr
    exact ⟨B,hB,θ,hθ,fun i hi => ⟨n i,hn i,hNB i,r i,hr i,hLe i,hData i hi⟩⟩
  · exact ⟨B,hB,1,by norm_num,fun i => (hI ⟨i⟩).elim⟩

end Hindman168
