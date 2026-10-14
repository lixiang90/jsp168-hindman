import Hindman168.RoughPolynomialCoefficientBound

namespace Hindman168
open Polynomial
open scoped BigOperators Classical

noncomputable def roughFixedLagrangeBasis (q : ℕ) (i : Fin (q + 1)) : ℝ[X] :=
  Lagrange.basis Finset.univ (fun j : Fin (q + 1) => (j.val : ℝ)) i

noncomputable def roughFixedInterpolationMass (q : ℕ) : ℝ :=
  1 + ∑ i : Fin (q + 1), ∑ j : Fin (q + 1),
    roughPolynomialCoeffMass (derivative^[j.val] (roughFixedLagrangeBasis q i))

theorem roughFixedInterpolationMass_pos (q : ℕ) : 0 < roughFixedInterpolationMass q := by
  have h : 0 ≤ ∑ i : Fin (q + 1), ∑ j : Fin (q + 1),
      roughPolynomialCoeffMass (derivative^[j.val] (roughFixedLagrangeBasis q i)) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => roughPolynomialCoeffMass_nonneg _))
  unfold roughFixedInterpolationMass
  linarith

theorem roughFixedLagrangeBasis_degree (q : ℕ) (i : Fin (q + 1)) :
    (roughFixedLagrangeBasis q i).natDegree = q := by
  have hinj : Set.InjOn (fun j : Fin (q + 1) => (j.val : ℝ)) (Finset.univ : Finset (Fin (q + 1))) := by
    intro j _ k _ h
    change (j.val : ℝ) = (k.val : ℝ) at h
    apply Fin.ext
    exact_mod_cast h
  simpa only [roughFixedLagrangeBasis, Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] using
    Lagrange.natDegree_basis hinj (Finset.mem_univ i)

theorem roughFixedInterpolationMass_derivative_sum (q j : ℕ) (hj : j ≤ q) :
    (∑ i : Fin (q + 1), roughPolynomialCoeffMass (derivative^[j] (roughFixedLagrangeBasis q i))) ≤
      roughFixedInterpolationMass q := by
  have h : (∑ i : Fin (q + 1), roughPolynomialCoeffMass (derivative^[j] (roughFixedLagrangeBasis q i))) ≤
      ∑ i : Fin (q + 1), ∑ k : Fin (q + 1),
        roughPolynomialCoeffMass (derivative^[k.val] (roughFixedLagrangeBasis q i)) := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (s := Finset.univ) (a := (⟨j, by omega⟩ : Fin (q + 1)))
      (f := fun k : Fin (q + 1) =>
      roughPolynomialCoeffMass (derivative^[k.val] (roughFixedLagrangeBasis q i)))
      (fun k _ => roughPolynomialCoeffMass_nonneg (derivative^[k.val] (roughFixedLagrangeBasis q i)))
      (Finset.mem_univ (⟨j, by omega⟩ : Fin (q + 1)))
  unfold roughFixedInterpolationMass
  linarith

theorem rough_fixed_interpolation_derivative_bound (q j : ℕ) (hj : j ≤ q)
    (values : Fin (q + 1) → ℝ) (eps : ℝ) (heps : 0 ≤ eps) (hv : ∀ i, |values i| ≤ eps)
    (B x : ℝ) (hB : 1 ≤ B) (hx : |x| ≤ B) :
    |(derivative^[j] (Lagrange.interpolate Finset.univ
      (fun i : Fin (q + 1) => (i.val : ℝ)) values)).eval x| ≤
      eps * roughFixedInterpolationMass q * B ^ q := by
  rw [Lagrange.interpolate_apply, iterate_derivative_sum, eval_finsetSum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hsum : (∑ i : Fin (q + 1),
      |(derivative^[j] (C (values i) * roughFixedLagrangeBasis q i)).eval x|) ≤
      ∑ i : Fin (q + 1), eps *
        roughPolynomialCoeffMass (derivative^[j] (roughFixedLagrangeBasis q i)) * B ^ q := by
    apply Finset.sum_le_sum
    intro i _
    rw [iterate_derivative_C_mul, eval_mul, eval_C, abs_mul]
    have hd : (derivative^[j] (roughFixedLagrangeBasis q i)).natDegree ≤ q := by
      apply (natDegree_iterate_derivative _ j).trans
      rw [roughFixedLagrangeBasis_degree]
      exact Nat.sub_le _ _
    have hb := rough_polynomial_eval_bound _ q hd B x hB hx
    calc
      |values i| * |(derivative^[j] (roughFixedLagrangeBasis q i)).eval x| ≤
          eps * (roughPolynomialCoeffMass (derivative^[j] (roughFixedLagrangeBasis q i)) * B ^ q) :=
        mul_le_mul (hv i) hb (abs_nonneg _) heps
      _ = _ := by ring
  apply hsum.trans
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (roughFixedInterpolationMass_derivative_sum q j hj) heps)
    (pow_nonneg (by linarith) q)

end Hindman168
