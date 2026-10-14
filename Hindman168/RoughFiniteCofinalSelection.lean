import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Push

namespace Hindman168
open scoped BigOperators

theorem rough_finite_diagonal_cofinal_selection {ι : Type*} [Fintype ι]
    (P : ι → ℕ → ℕ → Prop)
    (hP : ∀ n : ℕ, ∃ (j : ι) (H w : ℕ), n ≤ H ∧ n ≤ w ∧ P j H w) :
    ∃ j : ι, ∀ n : ℕ, ∃ H w : ℕ, n ≤ H ∧ n ≤ w ∧ P j H w := by
  classical
  by_contra hn
  push Not at hn
  choose cutoff hcutoff using hn
  let n := ∑ j, cutoff j
  obtain ⟨j, H, w, hH, hw, hp⟩ := hP n
  have hj : cutoff j ≤ n := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  exact hcutoff j H w (hj.trans hH) (hj.trans hw) hp

theorem rough_finite_cofinal_selection {ι : Type*} [Fintype ι]
    (P : ι → ℕ → ℕ → Prop)
    (hP : ∀ (H0 w0 : ℕ), ∃ (j : ι) (H w : ℕ), H0 ≤ H ∧ w0 ≤ w ∧ P j H w) :
    ∃ j : ι, ∀ H0 w0 : ℕ, ∃ H w : ℕ, H0 ≤ H ∧ w0 ≤ w ∧ P j H w := by
  obtain ⟨j, hj⟩ := rough_finite_diagonal_cofinal_selection P (fun n => hP n n)
  refine ⟨j, ?_⟩
  intro H0 w0
  obtain ⟨H, w, hH, hw, hp⟩ := hj (max H0 w0)
  exact ⟨H, w, (le_max_left H0 w0).trans hH, (le_max_right H0 w0).trans hw, hp⟩

end Hindman168
