import Hindman168.DyadicCoprimalityInduction

/-!
# The paper's two complete dyadic rough-coprimality estimates

Both events use the actual integer polynomial values on independent
normalized 1/p prime laws. The rough parts retain prime multiplicities.
The common constants and thresholds depend only on the fixed polynomial
pair, uniformly over all ratios between coordinate endpoints.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

def polynomialProductZeroEvent {m n : ℕ}
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ)
    (xy : (Fin m → ℕ) × (Fin n → ℕ)) : Prop :=
  MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F *
    MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G = 0

def roughPolynomialGcdEvent {m n : ℕ} (w : ℕ)
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ)
    (xy : (Fin m → ℕ) × (Fin n → ℕ)) : Prop :=
  MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F *
    MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G ≠ 0 ∧
  1 < (roughPartNat w (MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F).natAbs).gcd
    (roughPartNat w (MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G).natAbs)

theorem commonPrimeEvent_roughPolynomialGcdEvent {m n w : ℕ}
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ)
    (xy : (Fin m → ℕ) × (Fin n → ℕ)) :
    commonPrimeEvent w F G xy ↔ roughPolynomialGcdEvent w F G xy := by
  simpa only [roughPolynomialGcdEvent, mul_ne_zero_iff, and_assoc] using
    commonPrimeEvent_rough_gcd_iff F G xy

theorem dyadicCommonPrimeMass_rough_gcd {m n w : ℕ}
    (eF : Fin m → ℕ) (eG : Fin n → ℕ)
    (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ) :
    dyadicCommonPrimeMass eF eG w F G =
      event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
        (roughPolynomialGcdEvent w F G) := by
  unfold dyadicCommonPrimeMass
  congr 1
  funext xy
  exact propext (commonPrimeEvent_roughPolynomialGcdEvent F G xy)

theorem exists_unequalDyadicPrime_product_zero_bound {m n : ℕ}
    {F : MvPolynomial (Fin m) ℤ} {G : MvPolynomial (Fin n) ℤ}
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ e0 : ℕ, ∀ (eF : Fin m → ℕ) (eG : Fin n → ℕ),
      (∀ i, e0 ≤ eF i) → (∀ i, e0 ≤ eG i) → ∀ L : ℕ,
      Real.exp 1 ≤ (L : ℝ) → (∀ i, L ≤ 2 ^ eF i) → (∀ i, L ≤ 2 ^ eG i) →
      event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
        (polynomialProductZeroEvent F G) ≤
        (8 * ((∑ i, F.degreeOf i) + ∑ i, G.degreeOf i) : ℕ) * (Real.log (L : ℝ) / L) := by
  obtain ⟨en, hen⟩ := exists_dyadic_prime_normalization_threshold
  obtain ⟨e1, he1⟩ := unequalDyadicPrime_polynomial_zero_uniform hF
  obtain ⟨e2, he2⟩ := unequalDyadicPrime_polynomial_zero_uniform hG
  let e0 := max en (max e1 e2)
  refine ⟨e0, ?_⟩
  intro eF eG heF heG L hL hLF hLG
  have hHF : ∀ i, 0 < primePoolHarmonicMass (2 ^ eF i) (2 ^ (eF i + 1)) :=
    fun i => hen _ ((le_max_left _ _).trans (heF i))
  have hHG : ∀ i, 0 < primePoolHarmonicMass (2 ^ eG i) (2 ^ (eG i + 1)) :=
    fun i => hen _ ((le_max_left _ _).trans (heG i))
  have h1 := he1 eF (fun i => (le_max_left e1 e2).trans ((le_max_right en _).trans (heF i)))
    L hL hLF
  have h2 := he2 eG (fun i => (le_max_right e1 e2).trans ((le_max_right en _).trans (heG i)))
    L hL hLG
  have hp := event_or_le (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
    (fun xy => MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F = 0)
    (fun xy => MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G = 0)
    (tensor_nonneg _ _ (unequalDyadicPrimeMass_nonneg eF) (unequalDyadicPrimeMass_nonneg eG))
  rw [event_tensor_first (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG)
    (unequalDyadicPrimeMass_total eG hHG)
    (fun x : Fin m → ℕ => MvPolynomial.eval (fun i => (x i : ℤ)) F = 0),
    event_tensor_second (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG)
    (unequalDyadicPrimeMass_total eF hHF)
    (fun x : Fin n → ℕ => MvPolynomial.eval (fun i => (x i : ℤ)) G = 0)] at hp
  calc
    event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
        (polynomialProductZeroEvent F G) ≤
        event (unequalDyadicPrimeMass eF) (fun x => MvPolynomial.eval (fun i => (x i : ℤ)) F = 0) +
        event (unequalDyadicPrimeMass eG) (fun x => MvPolynomial.eval (fun i => (x i : ℤ)) G = 0) := by
      have hE : polynomialProductZeroEvent F G = (fun xy =>
          MvPolynomial.eval (fun i => (xy.1 i : ℤ)) F = 0 ∨
          MvPolynomial.eval (fun i => (xy.2 i : ℤ)) G = 0) := by
        funext xy
        exact propext mul_eq_zero
      rw [hE]
      exact hp
    _ ≤ (8 * ∑ i, (F.degreeOf i : ℝ)) * (Real.log (L : ℝ) / L) +
        (8 * ∑ i, (G.degreeOf i : ℝ)) * (Real.log (L : ℝ) / L) := add_le_add h1 h2
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_sum]; ring

theorem exists_unequalDyadicPrime_rough_coprimality_bounds {m n : ℕ}
    {F : MvPolynomial (Fin m) ℤ} {G : MvPolynomial (Fin n) ℤ}
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ w0 e0 K : ℕ, ∀ (eF : Fin m → ℕ) (eG : Fin n → ℕ),
      (∀ i, e0 ≤ eF i) → (∀ i, e0 ≤ eG i) → ∀ w L : ℕ,
      w0 ≤ w → 0 < w → Real.exp 2 ≤ (L : ℝ) →
      (∀ i, L ≤ 2 ^ eF i) → (∀ i, L ≤ 2 ^ eG i) →
      event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
        (polynomialProductZeroEvent F G) ≤ (K : ℝ) * (Real.log (L : ℝ) / L) ∧
      event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
        (roughPolynomialGcdEvent w F G) ≤ (K : ℝ) * dyadicCoprimeError w L := by
  obtain ⟨w0, ec, Kc, hc⟩ := exists_dyadic_common_prime_control hF hG
  obtain ⟨ez, hz⟩ := exists_unequalDyadicPrime_product_zero_bound hF hG
  let Kz := 8 * ((∑ i, F.degreeOf i) + ∑ i, G.degreeOf i)
  let K := Kz + Kc
  let e0 := max ec ez
  have hKz : Kz ≤ K := Nat.le_add_right _ _
  have hKc : Kc ≤ K := Nat.le_add_left _ _
  refine ⟨w0, e0, K, ?_⟩
  intro eF eG heF heG w L hww hw hL hLF hLG
  have hLone : Real.exp 1 ≤ (L : ℝ) :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hL
  have hlog : 0 ≤ Real.log (L : ℝ) / L :=
    div_nonneg (Real.log_nonneg
      ((Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans hLone))
      (Nat.cast_nonneg L)
  constructor
  · exact (hz eF eG (fun i => (le_max_right _ _).trans (heF i))
      (fun i => (le_max_right _ _).trans (heG i)) L hLone hLF hLG).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hKz) hlog)
  · rw [← dyadicCommonPrimeMass_rough_gcd eF eG F G]
    exact (hc eF eG (fun i => (le_max_left _ _).trans (heF i))
      (fun i => (le_max_left _ _).trans (heG i)) w L hww hw hL hLF hLG).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hKc) (dyadicCoprimeError_nonneg hL))

end Hindman168
