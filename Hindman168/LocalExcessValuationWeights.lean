import Hindman168.LocalExcessBeta
import Hindman168.ComparisonRowValuations

/-!
# Cancellation of the actual valuation mass against the local excess

The mass bound for the comparison row law cancels the sum of the row
valuations in beta. On the polynomial-test event it leaves the largest
valuation; off that event it leaves the actual largest distinct pair sum.
These are pointwise bounds for the original probability law.
-/

namespace Hindman168

open scoped BigOperators Classical

def rowValuationPolynomial {q : ℕ} (b : ℕ) (a : Fin q → ℕ) : ℝ :=
  ∏ i, ((a i + 1 : ℕ) : ℝ) ^ b

noncomputable def rowValuationWeight {q : ℕ} (p b : ℕ) (a : Fin q → ℕ) : ℝ :=
  rowValuationPolynomial b a * ((p : ℝ) ^ (∑ i, a i))⁻¹

theorem rowValuationPolynomial_nonneg {q : ℕ} (b : ℕ) (a : Fin q → ℕ) :
    0 ≤ rowValuationPolynomial b a := by
  unfold rowValuationPolynomial
  positivity

theorem rowValuationWeight_nonneg {q : ℕ} (p b : ℕ) (a : Fin q → ℕ) :
    0 ≤ rowValuationWeight p b a := by
  exact mul_nonneg (rowValuationPolynomial_nonneg b a) (by positivity)

theorem inverse_primePower_excess_le (p S T : ℕ) [NeZero p] (hTS : T ≤ S) :
    ((p : ℝ) ^ S)⁻¹ * (((p ^ (S - T) : ℕ) : ℝ) - 1) ≤
      ((p : ℝ) ^ T)⁻¹ := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  have he : (p : ℝ) ^ S = (p : ℝ) ^ (S - T) * (p : ℝ) ^ T := by
    rw [← pow_add, Nat.sub_add_cancel hTS]
  calc
    _ ≤ ((p : ℝ) ^ S)⁻¹ * (p : ℝ) ^ (S - T) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simp only [Nat.cast_pow]
      linarith
    _ = _ := by rw [he]; field_simp

theorem localExcessBeta_bad_weight_le {q : ℕ} (p b : ℕ) [NeZero p]
    (a : Fin q → ℕ) :
    rowValuationWeight p b a * localExcessBeta p a True ≤
      rowValuationPolynomial b a * ((p : ℝ) ^ rowMaxValuation a)⁻¹ := by
  by_cases h : (positiveRowSet a).card ≤ 1
  · rw [localExcessBeta_eq_zero_of_few a True h, mul_zero]
    exact mul_nonneg (rowValuationPolynomial_nonneg b a) (by positivity)
  · simp only [localExcessBeta, if_neg h, if_true, rowValuationWeight]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (inverse_primePower_excess_le p _ _ (rowMaxValuation_le_sum a))
      (rowValuationPolynomial_nonneg b a)

theorem localExcessBeta_good_weight_le {q : ℕ} (p b : ℕ) [NeZero p]
    (a : Fin q → ℕ) :
    rowValuationWeight p b a * localExcessBeta p a False ≤
      rowValuationPolynomial b a * ((p : ℝ) ^ rowTopTwoSum a)⁻¹ := by
  by_cases h : (positiveRowSet a).card ≤ 1
  · rw [localExcessBeta_eq_zero_of_few a False h, mul_zero]
    exact mul_nonneg (rowValuationPolynomial_nonneg b a) (by positivity)
  · simp only [localExcessBeta, if_neg h, if_false, rowValuationWeight]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (inverse_primePower_excess_le p _ _ (rowTopTwoSum_le_sum a))
      (rowValuationPolynomial_nonneg b a)

theorem comparisonRowPMF_beta_atom_le {q : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ)
    (hp : p.Prime) (hc : p.Coprime W) (a : Fin q → ℕ) (bad : Prop) :
    (((comparisonRowPMF s hs W).map (fun x i => (x i).factorization p)) a).toReal *
        localExcessBeta p a bad ≤
      rowValuationWeight p (Fintype.card κ) a * localExcessBeta p a bad := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact mul_le_mul_of_nonneg_right
    (comparisonRowPMF_valuation_atom_bound s hs W p hp hc a)
    (localExcessBeta_nonneg p a bad)

end Hindman168
