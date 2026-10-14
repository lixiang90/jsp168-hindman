import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic

namespace Hindman168
open scoped BigOperators Classical

theorem finite_rational_scalar_denominator {ι : Type*} [Fintype ι] (r : ι → ℚ) :
    ∃ n : ℕ, 0 < n ∧ ∀ i : ι, ∃ z : ℤ, (n : ℝ)*(r i : ℝ) = (z : ℝ) := by
  let n := ∏ i : ι, (r i).den
  have hn : 0 < n := Finset.prod_pos (fun i _ => (r i).den_pos)
  refine ⟨n,hn,?_⟩
  intro i
  have hdvd : (r i).den ∣ n := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  let t := n/(r i).den
  have ht : t*(r i).den=n := Nat.div_mul_cancel hdvd
  have hr : ((r i).den : ℚ)*r i = ((r i).num : ℚ) := by
    calc
      _ = ((r i).den : ℚ)*(((r i).num : ℚ)/(r i).den) :=
        congrArg (fun q : ℚ => ((r i).den : ℚ)*q) (r i).num_div_den.symm
      _ = _ := by
        have hd : ((r i).den : ℚ) ≠ 0 := by exact_mod_cast (r i).den_ne_zero
        field_simp
  refine ⟨(t : ℤ)*(r i).num,?_⟩
  have he : (n : ℚ)*r i = (((t : ℤ)*(r i).num : ℤ) : ℚ) := by
    rw [← ht,Nat.cast_mul,mul_assoc,hr,Int.cast_mul,Int.cast_natCast]
  exact_mod_cast he

end Hindman168
