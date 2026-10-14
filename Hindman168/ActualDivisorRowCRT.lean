import Hindman168.BoundedDivisorCRT
import Hindman168.DivisorMaskExpansion

/-!
# Exact normalized kernel counts for original row divisors

The original global modulus is the product of the original row divisors.
Reconstructing each divisor from its prime factors identifies its actual
normalized congruence count with the proved product of local alpha factors.
The integer linear-row divisibility test commutes with residue reduction.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem residueRowSystem_int_zero_iff (K q d : ℕ) (k : Fin q → ℕ)
    (hk : ∀ u, k u ∣ K) (c : Fin q → Fin d → ℤ) (x : Fin d → ℤ) :
    residueRowSystem K q d k hk c (fun j => (x j : ZMod K)) = 0 ↔
      ∀ u, (k u : ℤ) ∣ ∑ j, c u j * x j := by
  rw [residueRowSystem_zero_iff]
  apply forall_congr'
  intro u
  change ZMod.castHom (hk u) (ZMod (k u)) (∑ j, (c u j : ZMod K) * (x j : ZMod K)) = 0 ↔ _
  have hcast : (∑ j, (c u j : ZMod K) * (x j : ZMod K)) =
      ((∑ j, c u j * x j : ℤ) : ZMod K) := by simp
  rw [hcast, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

noncomputable def normalizedDivisorRowCount {q d : ℕ} (k : Fin q → ℕ)
    (c : Fin q → Fin d → ℤ) : ℝ :=
  if h : (∏ u, k u) = 0 then 0 else
    letI : NeZero (∏ u, k u) := ⟨h⟩
    ((∏ u, k u : ℕ) : ℝ) * event (uniformFintypeMass (Fin d → ZMod (∏ u, k u)))
      (fun x => residueRowSystem (∏ u, k u) q d k
        (fun u => Finset.dvd_prod_of_mem k (Finset.mem_univ u)) c x = 0)

theorem normalizedDivisorRowCount_of_ne_zero {q d : ℕ} (k : Fin q → ℕ)
    (hk : (∏ u, k u) ≠ 0) [NeZero (∏ u, k u)] (c : Fin q → Fin d → ℤ) :
    normalizedDivisorRowCount k c =
      ((∏ u, k u : ℕ) : ℝ) * event (uniformFintypeMass (Fin d → ZMod (∏ u, k u)))
        (fun x => residueRowSystem (∏ u, k u) q d k
          (fun u => Finset.dvd_prod_of_mem k (Finset.mem_univ u)) c x = 0) := by
  simp only [normalizedDivisorRowCount, dif_neg hk]

theorem uniform_divisor_row_event_congr (K L q d : ℕ) [NeZero K] [NeZero L]
    (hKL : K = L) (k l : Fin q → ℕ) (hkl : k = l)
    (hk : ∀ u, k u ∣ K) (hl : ∀ u, l u ∣ L) (c : Fin q → Fin d → ℤ) :
    event (uniformFintypeMass (Fin d → ZMod K))
      (fun x => residueRowSystem K q d k hk c x = 0) =
    event (uniformFintypeMass (Fin d → ZMod L))
      (fun x => residueRowSystem L q d l hl c x = 0) := by
  subst L
  subst l
  rfl

theorem actual_normalized_divisor_row_crt {q d : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (k : Fin q → ℕ) (hk : ∀ u, k u ≠ 0)
    (hcover : ∀ u, (k u).primeFactors ⊆ S) (c : Fin q → Fin d → ℤ) :
    normalizedDivisorRowCount k c =
      letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
      ∏ p : S, primePowerLocalAlpha (p : ℕ) q d
        (rowMaxValuation (fun u => (k u).factorization p))
        (fun u => (k u).factorization p)
        (rowValuation_le_max (fun u => (k u).factorization p)) c := by
  classical
  letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
  letI : NeZero (∏ p : S, (p : ℕ) ^ (∑ u, (k u).factorization p)) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (hS p p.property).ne_zero)⟩
  letI : NeZero (∏ u, k u) := ⟨Finset.prod_ne_zero_iff.mpr (fun u _ => hk u)⟩
  have hrow (u : Fin q) : (∏ p : S, (p : ℕ) ^ (k u).factorization p) = k u := by
    rw [Finset.prod_coe_sort S (fun p => p ^ (k u).factorization p)]
    exact primeValuationDivisor_full S hS (k u) (hk u) (hcover u)
  have h := normalized_primePower_kernel_crt (fun p : S => (p : ℕ)) q d
    (fun p u => (k u).factorization p)
    (primePowerModuli_pairwise_coprime (fun p : S => (p : ℕ))
      (fun p => hS p p.property) Subtype.val_injective (fun p => ∑ u, (k u).factorization p)) c
  have hQ : (∏ p : S, (p : ℕ) ^ (∑ u, (k u).factorization p)) = ∏ u, k u := by
    calc
      _ = ∏ u, ∏ p : S, (p : ℕ) ^ (k u).factorization p :=
        (rowPrimePower_divisor_product (fun p : S => (p : ℕ)) q
          (fun p u => (k u).factorization p)).symm
      _ = _ := Finset.prod_congr rfl (fun u _ => hrow u)
  have hc := uniform_divisor_row_event_congr _ _ q d hQ
    (fun u => ∏ p : S, (p : ℕ) ^ (k u).factorization p) k (funext hrow)
    (fun u => Finset.prod_dvd_prod_of_dvd _ _ (fun p _ =>
      pow_dvd_pow (p : ℕ) ((rowValuation_le_max (fun u => (k u).factorization p) u).trans
        (rowMaxValuation_le_sum (fun u => (k u).factorization p)))))
    (fun u => Finset.dvd_prod_of_mem k (Finset.mem_univ u)) c
  rw [hc] at h
  simp only [hrow] at h
  rw [normalizedDivisorRowCount_of_ne_zero k (NeZero.ne _) c]
  exact h

end Hindman168
