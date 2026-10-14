import Hindman168.ScalarTaylorTail
import Hindman168.IntegerWeightedModOneNorm

/-! Integer Taylor weights retain every ORIGINAL N^-i scale for h<=N. -/
namespace Hindman168
open Polynomial
open scoped BigOperators Classical

def scalarTaylorTailBudget (D : ℕ) : ℕ :=
  1+∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1), j.choose i

theorem scalar_taylor_tail_row_budget (D i : ℕ) (hi : i ≤ D) :
    (∑ j ∈ Finset.range (D+1), j.choose i) ≤ scalarTaylorTailBudget D := by
  have he := Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (D+1), j.choose i)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : i < D+1))
  dsimp [scalarTaylorTailBudget]
  omega

theorem scalar_integer_taylor_tail_norm (Q : ℝ[X]) (D M i h N : ℕ) (B : ℝ)
    (hi : i ≤ D) (hN : 0 < N) (hh : h ≤ N) (hB : 0 ≤ B)
    (S : Finset ℕ) (hS : S ⊆ Finset.range (D+1))
    (hIndex : ∀ j ∈ S, 3 ≤ j ∧ i ≤ j)
    (hCoeff : ∀ j : ℕ, 3 ≤ j → j ≤ D →
      (N : ℝ)^j*‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ B) :
    (N : ℝ)^i*‖(((M : ℝ)*(∑ j ∈ S, Q.coeff j*(j.choose i : ℝ)*(h : ℝ)^(j-i)) : ℝ) :
      UnitAddCircle)‖ ≤ (scalarTaylorTailBudget D : ℝ)*B := by
  let w : ℕ → ℤ := fun j => ((j.choose i*h^(j-i) : ℕ) : ℤ)
  let v : ℕ → ℝ := fun j => (M : ℝ)*Q.coeff j
  have he : (M : ℝ)*(∑ j ∈ S, Q.coeff j*(j.choose i : ℝ)*(h : ℝ)^(j-i)) =
      ∑ j ∈ S, (w j : ℝ)*v j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [w,v]
    push_cast
    ring
  rw [he]
  have hn := integer_weighted_mod_one_norm_bound S w v
  apply (mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (N : ℝ)^i)).trans
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ j ∈ S, (j.choose i : ℝ)*B := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hj3,hij⟩ := hIndex j hj
      have hjD : j ≤ D := by have := Finset.mem_range.mp (hS hj); omega
      have hw : |(w j : ℝ)| = (j.choose i : ℝ)*(h : ℝ)^(j-i) := by
        dsimp only [w]
        push_cast
        rw [abs_of_nonneg (by positivity)]
      have hpow : (h : ℝ)^(j-i) ≤ (N : ℝ)^(j-i) :=
        pow_le_pow_left₀ (Nat.cast_nonneg h) (by exact_mod_cast hh) _
      have hp : (N : ℝ)^i*(N : ℝ)^(j-i) = (N : ℝ)^j := by
        rw [← pow_add,Nat.add_sub_of_le hij]
      rw [hw]
      calc
        _ = (j.choose i : ℝ)*((N : ℝ)^i*(h : ℝ)^(j-i)*‖(v j : UnitAddCircle)‖) := by ring
        _ ≤ (j.choose i : ℝ)*((N : ℝ)^i*(N : ℝ)^(j-i)*‖(v j : UnitAddCircle)‖) := by
          gcongr
        _ = (j.choose i : ℝ)*((N : ℝ)^j*‖(v j : UnitAddCircle)‖) := by rw [hp]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hCoeff j hj3 hjD) (Nat.cast_nonneg _)
    _ ≤ ∑ j ∈ Finset.range (D+1), (j.choose i : ℝ)*B :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
    _ = (∑ j ∈ Finset.range (D+1), (j.choose i : ℝ))*B := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast scalar_taylor_tail_row_budget D i hi) hB

theorem scalar_taylor_tail_norm (Q : ℝ[X]) (D M i h N : ℕ) (B : ℝ)
    (hi : i ≤ D) (hi2 : 2 ≤ i) (hN : 0 < N) (hh : h ≤ N) (hB : 0 ≤ B)
    (hCoeff : ∀ j : ℕ, 3 ≤ j → j ≤ D →
      (N : ℝ)^j*‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ B) :
    (N : ℝ)^i*‖(((M : ℝ)*scalarTaylorTail Q D i h : ℝ) : UnitAddCircle)‖ ≤
      (scalarTaylorTailBudget D : ℝ)*B :=
  scalar_integer_taylor_tail_norm Q D M i h N B hi hN hh hB _ (Finset.filter_subset _ _)
    (fun j hj => by have := (Finset.mem_filter.mp hj).2; omega) hCoeff

theorem scalar_taylor_high_linear_tail_norm (Q : ℝ[X]) (D M h N : ℕ) (B : ℝ)
    (hD : 1 ≤ D) (hN : 0 < N) (hh : h ≤ N) (hB : 0 ≤ B)
    (hCoeff : ∀ j : ℕ, 3 ≤ j → j ≤ D →
      (N : ℝ)^j*‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ B) :
    (N : ℝ)*‖(((M : ℝ)*scalarTaylorHighLinearTail Q D h : ℝ) : UnitAddCircle)‖ ≤
      (scalarTaylorTailBudget D : ℝ)*B := by
  simpa only [scalarTaylorHighLinearTail,pow_one] using
    scalar_integer_taylor_tail_norm Q D M 1 h N B hD hN hh hB _ (Finset.filter_subset _ _)
      (fun j hj => by have := (Finset.mem_filter.mp hj).2; omega) hCoeff

end Hindman168
