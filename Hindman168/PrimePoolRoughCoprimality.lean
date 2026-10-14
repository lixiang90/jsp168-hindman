import Hindman168.DyadicRoughCoprimality
import Hindman168.DyadicPoolMixture

/-!
# Uniform rough coprimality for actual constructed prime pools

Each coordinate may have a different consecutive union of dyadic prime
intervals. The actual harmonic law is averaged over independent interval
choices. No bound on endpoint ratios or on the number of intervals enters
the resulting error constant.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem DyadicPrimePool.harmonicMass_pos_of_first (P : DyadicPrimePool)
    (h : 0 < primePoolHarmonicMass (2 ^ P.lowerExponent) (2 ^ (P.lowerExponent + 1))) :
    0 < P.harmonicMass := by
  have hAB : 2 ^ P.lowerExponent ≤ 2 ^ (P.lowerExponent + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hBC : 2 ^ (P.lowerExponent + 1) ≤ 2 ^ P.upperExponent :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by have := P.increasing; omega)
  unfold DyadicPrimePool.harmonicMass DyadicPrimePool.lower DyadicPrimePool.upper
  rw [primePoolHarmonicMass_split hAB hBC]
  exact add_pos_of_pos_of_nonneg h (primePoolHarmonicMass_nonneg _ _)

noncomputable def dyadicPoolTupleMass {n : ℕ} (P : Fin n → DyadicPrimePool) : Mass (Fin n → ℕ) :=
  piMass (fun i => primePoolMass (P i).lower (P i).upper)

theorem dyadicPoolTupleMass_nonneg {n : ℕ} (P : Fin n → DyadicPrimePool) (x : Fin n → ℕ) :
    0 ≤ dyadicPoolTupleMass P x :=
  piMass_nonneg _ (fun _ => primePoolMass_nonneg _ _) x

theorem dyadicPoolTupleMass_total {n : ℕ} (P : Fin n → DyadicPrimePool)
    (hH : ∀ i, 0 < (P i).harmonicMass) : total (dyadicPoolTupleMass P) = 1 :=
  piMass_total_one _ (fun i => primePoolMass_total (hH i))

theorem dyadicPoolTupleMass_dyadic_mixture {n : ℕ} (P : Fin n → DyadicPrimePool)
    (hH : ∀ i, 0 < (P i).harmonicMass) :
    dyadicPoolTupleMass P =
      mixture (Fintype.piFinset (fun i => Finset.Ico (P i).lowerExponent (P i).upperExponent))
        (fun e => ∏ i, dyadicPoolMixWeight (P i).lowerExponent (P i).upperExponent (e i))
        unequalDyadicPrimeMass := by
  classical
  letI : DecidableEq (Fin n) := instDecidableEqFin n
  have hc : (fun i => primePoolMass (P i).lower (P i).upper) =
      (fun i => mixture (Finset.Ico (P i).lowerExponent (P i).upperExponent)
        (dyadicPoolMixWeight (P i).lowerExponent (P i).upperExponent)
        (fun e => primePoolMass (2 ^ e) (2 ^ (e + 1)))) := by
    funext i
    exact primePoolMass_dyadic_mixture (P i).increasing.le (hH i)
  unfold dyadicPoolTupleMass
  rw [hc]
  exact piMass_mixtures (ι := Fin n) (κ := ℕ) (α := ℕ)
    (fun i => Finset.Ico (P i).lowerExponent (P i).upperExponent)
    (fun i => dyadicPoolMixWeight (P i).lowerExponent (P i).upperExponent)
    (fun _ e => primePoolMass (2 ^ e) (2 ^ (e + 1)))

theorem dyadicPoolTuple_event_uniform_le {m n : ℕ}
    (PF : Fin m → DyadicPrimePool) (PG : Fin n → DyadicPrimePool)
    (hHF : ∀ i, 0 < (PF i).harmonicMass) (hHG : ∀ i, 0 < (PG i).harmonicMass)
    (E : (Fin m → ℕ) × (Fin n → ℕ) → Prop) {B : ℝ}
    (hB : ∀ (eF : Fin m → ℕ) (eG : Fin n → ℕ),
      (∀ i, (PF i).lowerExponent ≤ eF i ∧ eF i < (PF i).upperExponent) →
      (∀ i, (PG i).lowerExponent ≤ eG i ∧ eG i < (PG i).upperExponent) →
      event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG)) E ≤ B) :
    event (tensor (dyadicPoolTupleMass PF) (dyadicPoolTupleMass PG)) E ≤ B := by
  classical
  rw [dyadicPoolTupleMass_dyadic_mixture PF hHF, dyadicPoolTupleMass_dyadic_mixture PG hHG]
  apply event_tensor_mixtures_uniform_le
  · intro e _
    exact Finset.prod_nonneg (fun i _ => dyadicPoolMixWeight_nonneg _ _ _)
  · intro e _
    exact Finset.prod_nonneg (fun i _ => dyadicPoolMixWeight_nonneg _ _ _)
  · rw [← Finset.prod_univ_sum]
    simp only [dyadicPoolMixWeight_total (PF _).increasing.le (hHF _), Finset.prod_const_one]
  · rw [← Finset.prod_univ_sum]
    simp only [dyadicPoolMixWeight_total (PG _).increasing.le (hHG _), Finset.prod_const_one]
  · intro eF heF eG heG
    apply hB eF eG
    · intro i
      exact Finset.mem_Ico.mp (Fintype.mem_piFinset.mp heF i)
    · intro i
      exact Finset.mem_Ico.mp (Fintype.mem_piFinset.mp heG i)

theorem exists_dyadicPool_rough_coprimality_bounds {m n : ℕ}
    {F : MvPolynomial (Fin m) ℤ} {G : MvPolynomial (Fin n) ℤ}
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ w0 e0 K : ℕ, ∀ (PF : Fin m → DyadicPrimePool) (PG : Fin n → DyadicPrimePool),
      (∀ i, e0 ≤ (PF i).lowerExponent) → (∀ i, e0 ≤ (PG i).lowerExponent) → ∀ w L : ℕ,
      w0 ≤ w → 0 < w → Real.exp 2 ≤ (L : ℝ) →
      (∀ i, L ≤ (PF i).lower) → (∀ i, L ≤ (PG i).lower) →
      event (tensor (dyadicPoolTupleMass PF) (dyadicPoolTupleMass PG))
        (polynomialProductZeroEvent F G) ≤ (K : ℝ) * (Real.log (L : ℝ) / L) ∧
      event (tensor (dyadicPoolTupleMass PF) (dyadicPoolTupleMass PG))
        (roughPolynomialGcdEvent w F G) ≤ (K : ℝ) * dyadicCoprimeError w L := by
  obtain ⟨w0, ec, K, hc⟩ := exists_unequalDyadicPrime_rough_coprimality_bounds hF hG
  obtain ⟨en, hen⟩ := exists_dyadic_prime_normalization_threshold
  let e0 := max ec en
  refine ⟨w0, e0, K, ?_⟩
  intro PF PG heF heG w L hww hw hL hLF hLG
  have hHF : ∀ i, 0 < (PF i).harmonicMass := fun i =>
    (PF i).harmonicMass_pos_of_first (hen _ ((le_max_right _ _).trans (heF i)))
  have hHG : ∀ i, 0 < (PG i).harmonicMass := fun i =>
    (PG i).harmonicMass_pos_of_first (hen _ ((le_max_right _ _).trans (heG i)))
  have hComponents : ∀ (eF : Fin m → ℕ) (eG : Fin n → ℕ),
      (∀ i, (PF i).lowerExponent ≤ eF i ∧ eF i < (PF i).upperExponent) →
      (∀ i, (PG i).lowerExponent ≤ eG i ∧ eG i < (PG i).upperExponent) →
      event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
        (polynomialProductZeroEvent F G) ≤ (K : ℝ) * (Real.log (L : ℝ) / L) ∧
      event (tensor (unequalDyadicPrimeMass eF) (unequalDyadicPrimeMass eG))
        (roughPolynomialGcdEvent w F G) ≤ (K : ℝ) * dyadicCoprimeError w L := by
    intro eF eG hmF hmG
    exact hc eF eG
      (fun i => ((le_max_left _ _).trans (heF i)).trans (hmF i).1)
      (fun i => ((le_max_left _ _).trans (heG i)).trans (hmG i).1)
      w L hww hw hL
      (fun i => (hLF i).trans (Nat.pow_le_pow_right (by decide : 0 < 2) (hmF i).1))
      (fun i => (hLG i).trans (Nat.pow_le_pow_right (by decide : 0 < 2) (hmG i).1))
  constructor
  · exact dyadicPoolTuple_event_uniform_le PF PG hHF hHG _
      (fun eF eG hmF hmG => (hComponents eF eG hmF hmG).1)
  · exact dyadicPoolTuple_event_uniform_le PF PG hHF hHG _
      (fun eF eG hmF hmG => (hComponents eF eG hmF hmG).2)

end Hindman168
