import Hindman168.DyadicPrimeFiberEvents

/-!
# Common large prime divisors after exposing the smaller tuple

The exposed tuple has every endpoint at most A; the independent tuple's
main endpoint is at least A. The set of prime tests is the actual finite
set of large prime factors of the exposed value. Leading-coefficient
divisibility in the other tuple remains excluded and must be handled by
the variable induction. No complete rough-coprimality claim is made here.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem unequalDyadicPrime_supported_coordinate_bound {m A : ℕ}
    (e : Fin m → ℕ) (hA : ∀ i, 2 ^ e i ≤ A) (x : Fin m → ℕ)
    (hx : x ∈ (unequalDyadicPrimeMass e).support) (i : Fin m) : x i ≤ 2 * A := by
  have hp : (∏ j, primePoolMass (2 ^ e j) (2 ^ (e j + 1)) (x j)) ≠ 0 :=
    Finsupp.mem_support_iff.mp hx
  have hs := Finsupp.mem_support_iff.mpr (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i))
  have hm := primePool_mem.mp (primePoolMass_support _ _ hs)
  have hu : x i < 2 * 2 ^ e i := by
    simpa only [Nat.pow_succ, Nat.mul_comm] using hm.2.1
  exact hu.le.trans (Nat.mul_le_mul_left 2 (hA i))

theorem unequalDyadicPrime_largePrimeDivisors_card_bound {m A : ℕ}
    (e : Fin m → ℕ) (f : MvPolynomial (Fin m) ℤ)
    (hA : 2 ≤ A) (hmax : ∀ i, 2 ^ e i ≤ A)
    (hsize : (integerPolynomialDyadicSize f) ^ 2 ≤ A) (x : Fin m → ℕ)
    (hx : x ∈ (unequalDyadicPrimeMass e).support) :
    (largePrimeDivisors A (MvPolynomial.eval (fun i => (x i : ℤ)) f).natAbs).card ≤
      2 * f.totalDegree + 1 := by
  by_cases hz : MvPolynomial.eval (fun i => (x i : ℤ)) f = 0
  · simp only [hz, Int.natAbs_zero, largePrimeDivisors, Nat.primeFactors_zero,
      Finset.filter_empty, Finset.card_empty, Nat.zero_le]
  · apply integerPolynomial_largePrimeDivisors_card_le f _ hA _ hz hsize
    intro i
    simpa only [Int.natAbs_natCast] using unequalDyadicPrime_supported_coordinate_bound e hmax x hx i

theorem unequalDyadicPrime_common_large_divisor_bound {m n A : ℕ}
    (eF : Fin m → ℕ) (eG : Fin (n + 1) → ℕ)
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ)
    (hHF : ∀ i, 0 < primePoolHarmonicMass (2 ^ eF i) (2 ^ (eF i + 1)))
    (hHG : ∀ i, 0 < primePoolHarmonicMass (2 ^ eG i) (2 ^ (eG i + 1)))
    (hA : 2 ≤ A) (hAexp : Real.exp 2 ≤ (A : ℝ))
    (hFmax : ∀ i, 2 ^ eF i ≤ A) (hGmain : A ≤ 2 ^ eG 0)
    (hsize : (integerPolynomialDyadicSize F) ^ 2 ≤ A)
    (hPNT : 1 / (8 * Real.log (2 ^ eG 0 : ℕ)) ≤
      primePoolHarmonicMass (2 ^ eG 0) (2 ^ (eG 0 + 1)))
    (hsmall : ∀ q : ℕ, q.Prime → (q : ℝ) ≤ Real.sqrt (2 ^ eG 0 : ℕ) →
      ∀ a < q, primePoolResidueMass q (2 ^ eG 0) (2 ^ (eG 0 + 1)) a ≤ 1032 / (q : ℝ)) :
    event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG)) (fun xy =>
      MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F ≠ 0 ∧
      ∃ q : ℕ, q.Prime ∧ Real.sqrt (A : ℝ) < q ∧
        (q : ℤ) ∣ MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F ∧
        ¬ (q : ℤ) ∣ MvPolynomial.eval (fun i => (Fin.tail xy.2 i : ℤ))
          (integerPolynomialMainLeading G) ∧
        (q : ℤ) ∣ MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G) ≤
      (2 * F.totalDegree + 1 : ℕ) * (G.degreeOf 0 : ℝ) *
        (1032 * Real.log (A : ℝ) / Real.sqrt A) := by
  let S := fun x : Fin m → ℕ =>
    largePrimeDivisors A (MvPolynomial.eval (fun i => (x i : ℤ)) F).natAbs
  let E := fun (_x : Fin m → ℕ) (q : ℕ) (y : Fin (n + 1) → ℕ) =>
    ¬ (q : ℤ) ∣ MvPolynomial.eval (fun i => (Fin.tail y i : ℤ))
      (integerPolynomialMainLeading G) ∧
    (q : ℤ) ∣ MvPolynomial.eval (fun i => (y i : ℤ)) G
  have hlog : 0 ≤ Real.log (A : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 2) hAexp
    rw [Real.log_exp] at h
    linarith
  have hb : 0 ≤ (G.degreeOf 0 : ℝ) * (1032 * Real.log (A : ℝ) / Real.sqrt A) := by positivity
  have hu := event_tensor_varying_union_le (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG)
    S E (unequalDyadicPrimeMass_nonneg eF) (unequalDyadicPrimeMass_nonneg eG)
    (unequalDyadicPrimeMass_total eF hHF)
    (K := 2 * F.totalDegree + 1)
    (fun x hx => unequalDyadicPrime_largePrimeDivisors_card_bound eF F hA hFmax hsize x hx) hb
    (by
      intro x _ q hq
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
      letI : Fact q.Prime := ⟨hqp⟩
      have hql : Real.sqrt (A : ℝ) < q := sqrt_lt_prime_iff_square_lt.mpr (Finset.mem_filter.mp hq).2
      exact unequalDyadicPrime_main_large_divisibility_bound eG hHG hAexp hGmain
        (hA.trans hGmain) hPNT (hsmall q hqp) hql G)
  calc
    _ ≤ event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
        (fun xy => ∃ q ∈ S xy.1, E xy.1 q xy.2) := by
      apply event_mono _ (tensor_nonneg _ _ (unequalDyadicPrimeMass_nonneg eF)
        (unequalDyadicPrimeMass_nonneg eG))
      rintro xy ⟨hn, q, hqp, hql, hqF, hqGlead, hqG⟩
      refine ⟨q, (mem_largePrimeDivisors (Int.natAbs_ne_zero.mpr hn)).mpr
        ⟨hqp, Int.natCast_dvd.mp hqF, sqrt_lt_prime_iff_square_lt.mp hql⟩, hqGlead, hqG⟩
    _ ≤ (2 * F.totalDegree + 1 : ℕ) *
        ((G.degreeOf 0 : ℝ) * (1032 * Real.log (A : ℝ) / Real.sqrt A)) := hu
    _ = _ := by ring

end Hindman168
