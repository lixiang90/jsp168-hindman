import Hindman168.SmallPrimeCommonDivisors
import Hindman168.DyadicLargePrimeCoprimality
import Hindman168.PrimeGoodSamples

/-!
# The regular part of dyadic rough coprimality

This combines the small and large prime branches with the actual sieve
and PNT estimates. A regular common prime divides neither main leading
coefficient. The omitted leading-coefficient events are not bounded here;
they remain the induction step of the full rough-coprimality lemma.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

def primePolynomialMainTest {n : ℕ} (q : ℕ) (f : MvPolynomial (Fin (n + 1)) ℤ)
    (x : Fin (n + 1) → ℕ) : Prop :=
  ¬ (q : ℤ) ∣ MvPolynomial.eval (fun i => (Fin.tail x i : ℤ)) (integerPolynomialMainLeading f) ∧
    (q : ℤ) ∣ MvPolynomial.eval (fun i => (x i : ℤ)) f

def regularCommonPrimeEvent {m n : ℕ} (w : ℕ)
    (F : MvPolynomial (Fin (m + 1)) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ)
    (xy : (Fin (m + 1) → ℕ) × (Fin (n + 1) → ℕ)) : Prop :=
  MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F ≠ 0 ∧
    ∃ q : ℕ, q.Prime ∧ w < q ∧ primePolynomialMainTest q F xy.1 ∧ primePolynomialMainTest q G xy.2

theorem dyadic_regular_common_prime_bound {m n w : ℕ} (hw : 0 < w)
    (eF : Fin (m + 1) → ℕ) (eG : Fin (n + 1) → ℕ)
    (F : MvPolynomial (Fin (m + 1)) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ)
    (hHF : ∀ i, 0 < primePoolHarmonicMass (2 ^ eF i) (2 ^ (eF i + 1)))
    (hHG : ∀ i, 0 < primePoolHarmonicMass (2 ^ eG i) (2 ^ (eG i + 1)))
    (hA : 2 ≤ 2 ^ eF 0) (hAexp : Real.exp 2 ≤ (2 ^ eF 0 : ℕ))
    (hFmax : ∀ i, 2 ^ eF i ≤ 2 ^ eF 0) (hGmain : 2 ^ eF 0 ≤ 2 ^ eG 0)
    (hsize : (integerPolynomialDyadicSize F) ^ 2 ≤ 2 ^ eF 0)
    (hPNT : 1 / (8 * Real.log (2 ^ eG 0 : ℕ)) ≤
      primePoolHarmonicMass (2 ^ eG 0) (2 ^ (eG 0 + 1)))
    (hcapF : ∀ q : ℕ, q.Prime → (q : ℝ) ≤ Real.sqrt (2 ^ eF 0 : ℕ) →
      ∀ a < q, primePoolResidueMass q (2 ^ eF 0) (2 ^ (eF 0 + 1)) a ≤ 1032 / (q : ℝ))
    (hcapG : ∀ q : ℕ, q.Prime → (q : ℝ) ≤ Real.sqrt (2 ^ eG 0 : ℕ) →
      ∀ a < q, primePoolResidueMass q (2 ^ eG 0) (2 ^ (eG 0 + 1)) a ≤ 1032 / (q : ℝ)) :
    event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
      (regularCommonPrimeEvent w F G) ≤
      1032 ^ 2 * (F.degreeOf 0 : ℝ) * (G.degreeOf 0 : ℝ) / (w : ℝ) +
        (2 * F.totalDegree + 1 : ℕ) * (G.degreeOf 0 : ℝ) *
          (1032 * Real.log (2 ^ eF 0 : ℕ) / Real.sqrt (2 ^ eF 0 : ℕ)) := by
  let A := 2 ^ eF 0
  let S := (Nat.primesLE A).filter (fun q => w < q ∧ q ^ 2 ≤ A)
  let ES := fun xy : (Fin (m + 1) → ℕ) × (Fin (n + 1) → ℕ) =>
    ∃ q ∈ S, primePolynomialMainTest q F xy.1 ∧ primePolynomialMainTest q G xy.2
  let EL := fun xy : (Fin (m + 1) → ℕ) × (Fin (n + 1) → ℕ) =>
    MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F ≠ 0 ∧
      ∃ q : ℕ, q.Prime ∧ Real.sqrt (A : ℝ) < q ∧
        (q : ℤ) ∣ MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F ∧
        ¬ (q : ℤ) ∣ MvPolynomial.eval (fun i => (Fin.tail xy.2 i : ℤ))
          (integerPolynomialMainLeading G) ∧
        (q : ℤ) ∣ MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G
  have hqp : ∀ q ∈ S, q.Prime := fun q hq => Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hq).1
  have hqs : ∀ q ∈ S, (q : ℝ) ≤ Real.sqrt A := by
    intro q hq
    apply le_of_not_gt
    intro h
    exact (Finset.mem_filter.mp hq).2.2.not_gt (sqrt_lt_prime_iff_square_lt.mp h)
  have hs := unequalDyadicPrime_common_small_divisor_bound hw S hqp
    (fun q hq => (Finset.mem_filter.mp hq).2.1) eF eG F G hHF hHG
    (fun q hq => hcapF q (hqp q hq) (hqs q hq))
    (fun q hq => hcapG q (hqp q hq)
      ((hqs q hq).trans (Real.sqrt_le_sqrt (by exact_mod_cast hGmain))))
  have hl := unequalDyadicPrime_common_large_divisor_bound eF eG F G hHF hHG
    hA hAexp hFmax hGmain hsize hPNT hcapG
  have hm := event_mono (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
    (tensor_nonneg _ _ (unequalDyadicPrimeMass_nonneg eF) (unequalDyadicPrimeMass_nonneg eG))
    (E := regularCommonPrimeEvent w F G) (F := fun xy => ES xy ∨ EL xy) (by
      rintro xy ⟨hn, q, hp, hwq, hqF, hqG⟩
      by_cases hqA : q ^ 2 ≤ A
      · apply Or.inl
        have hqa : q ≤ A := by nlinarith [hp.two_le]
        exact ⟨q, Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hqa, hp⟩, hwq, hqA⟩, hqF, hqG⟩
      · exact Or.inr ⟨hn, q, hp, sqrt_lt_prime_iff_square_lt.mpr (by omega), hqF.2, hqG⟩)
  exact hm.trans ((event_or_le _ ES EL
    (tensor_nonneg _ _ (unequalDyadicPrimeMass_nonneg eF) (unequalDyadicPrimeMass_nonneg eG))).trans
      (add_le_add hs hl))

theorem exists_dyadic_regular_common_prime_threshold {m n : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ) :
    ∃ e0 : ℕ, ∀ (eF : Fin (m + 1) → ℕ) (eG : Fin (n + 1) → ℕ),
      (∀ i, e0 ≤ eF i) → (∀ i, e0 ≤ eG i) →
      (∀ i, eF i ≤ eF 0) → eF 0 ≤ eG 0 → ∀ w : ℕ, 0 < w →
      event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
        (regularCommonPrimeEvent w F G) ≤
        1032 ^ 2 * (F.degreeOf 0 : ℝ) * (G.degreeOf 0 : ℝ) / (w : ℝ) +
          (2 * F.totalDegree + 1 : ℕ) * (G.degreeOf 0 : ℝ) *
            (1032 * Real.log (2 ^ eF 0 : ℕ) / Real.sqrt (2 ^ eF 0 : ℕ)) := by
  obtain ⟨ez, hez⟩ := exists_uniform_dyadic_zero_threshold
  obtain ⟨es, hes⟩ := exists_dyadicSmallPrimeResidue_threshold
  have hexp := (tendsto_natCast_atTop_atTop.comp dyadic_atTop).eventually
    (eventually_ge_atTop (Real.exp 2))
  have hsize := dyadic_atTop.eventually (eventually_ge_atTop ((integerPolynomialDyadicSize F) ^ 2))
  obtain ⟨et, het⟩ := eventually_atTop.mp (hexp.and hsize)
  let e0 := max ez (max es et)
  have hzero : ∀ e ≥ e0, 2 ≤ 2 ^ e ∧
      1 / (8 * Real.log (2 ^ e : ℕ)) ≤ primePoolHarmonicMass (2 ^ e) (2 ^ (e + 1)) :=
    fun e he => hez e ((le_max_left _ _).trans he)
  have hpos : ∀ e ≥ e0, 0 < primePoolHarmonicMass (2 ^ e) (2 ^ (e + 1)) := by
    intro e he
    have hlog : 0 < Real.log (2 ^ e : ℕ) :=
      Real.log_pos (by exact_mod_cast (by have := (hzero e he).1; omega : 1 < 2 ^ e))
    exact (one_div_pos.mpr (mul_pos (by norm_num) hlog)).trans_le (hzero e he).2
  have hres : ∀ e ≥ e0, ∀ q : ℕ, q.Prime → (q : ℝ) ≤ Real.sqrt (2 ^ e : ℕ) →
      ∀ a < q, primePoolResidueMass q (2 ^ e) (2 ^ (e + 1)) a ≤ 1032 / (q : ℝ) :=
    fun e he => hes e ((le_max_left es et).trans ((le_max_right ez _).trans he))
  refine ⟨e0, ?_⟩
  intro eF eG heF heG hmax hmain w hw
  have ht := het (eF 0) ((le_max_right es et).trans ((le_max_right ez _).trans (heF 0)))
  apply dyadic_regular_common_prime_bound hw eF eG F G
    (fun i => hpos _ (heF i)) (fun i => hpos _ (heG i))
    (hzero _ (heF 0)).1 ht.1 _ _ ht.2 (hzero _ (heG 0)).2
    (hres _ (heF 0)) (hres _ (heG 0))
  · intro i
    exact Nat.pow_le_pow_right (by decide) (hmax i)
  · exact Nat.pow_le_pow_right (by decide) hmain

theorem dyadic_regular_common_prime_uniform_endpoint {m n : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ) :
    ∃ e0 : ℕ, ∀ (eF : Fin (m + 1) → ℕ) (eG : Fin (n + 1) → ℕ),
      (∀ i, e0 ≤ eF i) → (∀ i, e0 ≤ eG i) →
      (∀ i, eF i ≤ eF 0) → eF 0 ≤ eG 0 →
      ∀ w L : ℕ, 0 < w → Real.exp 2 ≤ (L : ℝ) → L ≤ 2 ^ eF 0 →
      event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
        (regularCommonPrimeEvent w F G) ≤
        1032 ^ 2 * (F.degreeOf 0 : ℝ) * (G.degreeOf 0 : ℝ) / (w : ℝ) +
          (2 * F.totalDegree + 1 : ℕ) * (G.degreeOf 0 : ℝ) *
            (1032 * Real.log (L : ℝ) / Real.sqrt L) := by
  obtain ⟨e0, he0⟩ := exists_dyadic_regular_common_prime_threshold F G
  refine ⟨e0, ?_⟩
  intro eF eG heF heG hmax hmain w L hw hL hLA
  have hLAr : (L : ℝ) ≤ (2 ^ eF 0 : ℕ) := by exact_mod_cast hLA
  have hm := Real.log_div_sqrt_antitoneOn hL (hL.trans hLAr) hLAr
  apply (he0 eF eG heF heG hmax hmain w hw).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 1032)

end Hindman168
