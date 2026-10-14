import Hindman168.RoughFiniteCofinalSelection
import Hindman168.RoughResidueScaleGrowth
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Hindman168
open Filter

theorem rough_cofinal_strict_subsequence (P : ℕ → Prop)
    (h : ∀ n : ℕ, ∃ w : ℕ, n ≤ w ∧ P w) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, P (f n) := by
  classical
  choose next hnext hP using h
  let f : ℕ → ℕ := fun n => Nat.rec (next 0) (fun _ w => next (w+1)) n
  have hp : ∀ n, P (f n) := by
    intro n
    cases n <;> exact hP _
  have hm : StrictMono f := strictMono_nat_of_lt_succ (fun n => by
    change f n < next (f n+1)
    exact (Nat.lt_succ_self _).trans_le (hnext _))
  exact ⟨f, hm, hp⟩

/-- Downward closure in length upgrades joint cofinality to infinitely many
scale indices at each fixed length, on one fixed member of the finite list. -/
theorem rough_finite_lengthwise_subsequences {ι : Type*} [Fintype ι]
    (P : ι → ℕ → ℕ → Prop)
    (hdown : ∀ j H H' w, H ≤ H' → P j H' w → P j H w)
    (h : ∀ H0 w0 : ℕ, ∃ (j : ι) (H w : ℕ), H0 ≤ H ∧ w0 ≤ w ∧ P j H w) :
    ∃ j : ι, ∀ H : ℕ, ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, P j H (f n) := by
  obtain ⟨j, hj⟩ := rough_finite_cofinal_selection P h
  refine ⟨j, fun H => rough_cofinal_strict_subsequence (P j H) ?_⟩
  intro n
  obtain ⟨H', w, hH, hw, hp⟩ := hj H n
  exact ⟨w, hw, hdown j H H' w hH hp⟩

theorem rough_subsequence_rescaled_growth {S Z : ℕ → ℝ}
    (h : PowerDominates atTop Z S) (K : ℝ) (hK : 0 < K)
    (f : ℕ → ℕ) (hf : StrictMono f) :
    PowerDominates atTop (fun n => Z (f n)/K) (fun n => S (f n)) := by
  intro d
  exact (rough_residue_scale_power_dominates h K hK d).comp_tendsto hf.tendsto_atTop

end Hindman168
