import Hindman168.PrimeValuationGeometric

/-!
# Finite joint prime-valuation PMF identification

Every finite vector pushforward of the actual W-unit power law has atoms
equal to products of the actual geometric prime-valuation atoms.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def extendPrimeVector (S : Finset ℕ) (a : S → ℕ) (p : ℕ) : ℕ := by
  classical
  exact if hp : p ∈ S then a ⟨p, hp⟩ else 0

theorem extendPrimeVector_mem (S : Finset ℕ) (a : S → ℕ) (p : S) :
    extendPrimeVector S a p = a p := by
  simp [extendPrimeVector, p.property]

theorem primeVector_eq_iff (S : Finset ℕ) (a : S → ℕ) (n : ℕ) :
    a = (fun p : S => n.factorization p) ↔
      ∀ p ∈ S, n.factorization p = extendPrimeVector S a p := by
  constructor
  · intro he p hp
    have h := congrFun he ⟨p, hp⟩
    simpa only [extendPrimeVector, dif_pos hp] using h.symm
  · intro h
    funext p
    simpa only [extendPrimeVector_mem] using (h p p.property).symm

theorem powerUnitPMF_prime_vector_apply {s : ℝ} (hs : 1 < s)
    (W : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hW : ∀ p ∈ S, p.Coprime W) (a : S → ℕ) :
    ((powerUnitPMF s hs W).map (fun n => fun p : S => n.factorization p)) a =
      ENNReal.ofReal (∏ p : S, primeValuationMass s p (a p)) := by
  classical
  rw [powerUnitPMF_map_apply]
  simp only [primeVector_eq_iff]
  rw [powerUnitProbability_valuation_vector_tsum hs W S (extendPrimeVector S a) hS hW]
  congr 1
  rw [← Finset.prod_attach]
  simp only [primeValuationMass, extendPrimeVector_mem, Finset.univ_eq_attach]

theorem powerUnitPMF_prime_vector_product {s : ℝ} (hs : 1 < s)
    (W : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hW : ∀ p ∈ S, p.Coprime W) (a : S → ℕ) :
    ((powerUnitPMF s hs W).map (fun n => fun p : S => n.factorization p)) a =
      ∏ p : S, ((powerUnitPMF s hs W).map (fun n => n.factorization p)) (a p) := by
  classical
  rw [powerUnitPMF_prime_vector_apply hs W S hS hW]
  simp only [powerUnitPMF_prime_valuation hs W _ (hS _ (Subtype.prop _))
    (hW _ (Subtype.prop _)), primeValuationPMF_apply]
  exact ENNReal.ofReal_prod_of_nonneg
    (fun p _ => primeValuationMass_nonneg hs (hS p p.property).two_le (a p))

end Hindman168
