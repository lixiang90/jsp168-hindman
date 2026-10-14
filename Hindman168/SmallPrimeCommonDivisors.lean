import Hindman168.DyadicPrimeFiberEvents
import Mathlib.Analysis.PSeries

/-!
# Summing two independent small-prime divisibility tests

The finite reciprocal-square tail is at most 1/w. Outside both main
leading-coefficient exceptions, independent polynomial tests each cost
at most 1032 times the main degree divided by the modulus prime. Their
common-prime union is bounded without counting primes or changing weights.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem reciprocal_square_finset_tail_le {w : ℕ} (hw : 0 < w) (S : Finset ℕ)
    (hS : ∀ q ∈ S, w < q) :
    (∑ q ∈ S, ((q : ℝ) ^ 2)⁻¹) ≤ 1 / (w : ℝ) := by
  let N := max w (S.sup id)
  have hs : S ⊆ Finset.Ioc w N := by
    intro q hq
    exact Finset.mem_Ioc.mpr ⟨hS q hq,
      (Finset.le_sup (f := id) hq).trans (le_max_right _ _)⟩
  have hi := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := w) (n := N) hw.ne' (le_max_left _ _)
  calc
    _ ≤ ∑ q ∈ Finset.Ioc w N, ((q : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
    _ ≤ (w : ℝ)⁻¹ - (N : ℝ)⁻¹ := hi
    _ ≤ 1 / (w : ℝ) := by rw [one_div]; exact sub_le_self _ (by positivity)

theorem unequalDyadicPrime_common_small_divisor_bound {m n w : ℕ}
    (hw : 0 < w) (S : Finset ℕ) (hprime : ∀ q ∈ S, q.Prime)
    (hcut : ∀ q ∈ S, w < q)
    (eF : Fin (m + 1) → ℕ) (eG : Fin (n + 1) → ℕ)
    (F : MvPolynomial (Fin (m + 1)) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ)
    (hHF : ∀ i, 0 < primePoolHarmonicMass (2 ^ eF i) (2 ^ (eF i + 1)))
    (hHG : ∀ i, 0 < primePoolHarmonicMass (2 ^ eG i) (2 ^ (eG i + 1)))
    (hcapF : ∀ q ∈ S, ∀ a < q,
      primePoolResidueMass q (2 ^ eF 0) (2 ^ (eF 0 + 1)) a ≤ 1032 / (q : ℝ))
    (hcapG : ∀ q ∈ S, ∀ a < q,
      primePoolResidueMass q (2 ^ eG 0) (2 ^ (eG 0 + 1)) a ≤ 1032 / (q : ℝ)) :
    event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG)) (fun xy =>
      ∃ q ∈ S,
        (¬ (q : ℤ) ∣ MvPolynomial.eval (fun i => (Fin.tail xy.1 i : ℤ))
          (integerPolynomialMainLeading F) ∧
          (q : ℤ) ∣ MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F) ∧
        (¬ (q : ℤ) ∣ MvPolynomial.eval (fun i => (Fin.tail xy.2 i : ℤ))
          (integerPolynomialMainLeading G) ∧
          (q : ℤ) ∣ MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G)) ≤
      1032 ^ 2 * (F.degreeOf 0 : ℝ) * (G.degreeOf 0 : ℝ) / (w : ℝ) := by
  let EF := fun (q : ℕ) (x : Fin (m + 1) → ℕ) =>
    ¬ (q : ℤ) ∣ MvPolynomial.eval (fun i => (Fin.tail x i : ℤ))
      (integerPolynomialMainLeading F) ∧
    (q : ℤ) ∣ MvPolynomial.eval (fun i => (x i : ℤ)) F
  let EG := fun (q : ℕ) (x : Fin (n + 1) → ℕ) =>
    ¬ (q : ℤ) ∣ MvPolynomial.eval (fun i => (Fin.tail x i : ℤ))
      (integerPolynomialMainLeading G) ∧
    (q : ℤ) ∣ MvPolynomial.eval (fun i => (x i : ℤ)) G
  have hu := event_tensor_common_test_union_le (unequalDyadicPrimeMass eF)
    (unequalDyadicPrimeMass eG) S EF EG (unequalDyadicPrimeMass_nonneg eF)
    (unequalDyadicPrimeMass_nonneg eG)
    (fun q => (F.degreeOf 0 : ℝ) * (1032 / (q : ℝ)))
    (fun q => (G.degreeOf 0 : ℝ) * (1032 / (q : ℝ)))
    (fun _ _ => by positivity)
    (by intro q hq; letI : Fact q.Prime := ⟨hprime q hq⟩
        exact unequalDyadicPrime_main_small_divisibility_bound eF hHF (hcapF q hq) F)
    (by intro q hq; letI : Fact q.Prime := ⟨hprime q hq⟩
        exact unequalDyadicPrime_main_small_divisibility_bound eG hHG (hcapG q hq) G)
  calc
    _ ≤ ∑ q ∈ S, ((F.degreeOf 0 : ℝ) * (1032 / (q : ℝ))) *
        ((G.degreeOf 0 : ℝ) * (1032 / (q : ℝ))) := hu
    _ = (1032 ^ 2 * (F.degreeOf 0 : ℝ) * (G.degreeOf 0 : ℝ)) *
        (∑ q ∈ S, ((q : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      simp only [div_eq_mul_inv]
      ring
    _ ≤ (1032 ^ 2 * (F.degreeOf 0 : ℝ) * (G.degreeOf 0 : ℝ)) * (1 / (w : ℝ)) :=
      mul_le_mul_of_nonneg_left (reciprocal_square_finset_tail_le hw S hcut) (by positivity)
    _ = _ := by ring

end Hindman168
