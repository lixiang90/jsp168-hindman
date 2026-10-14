import Hindman168.ComparisonDivisorValuations
import Hindman168.PowerUnitJointValuationPMF

/-!
# Prime independence after multiplying actual raw comparison draws

Coordinatewise pushforward, matrix transposition, and summing each prime
column identify the actual joint valuation law of the divisor. The formula
is derived from the original raw product PMF and its actual marginals.
-/

namespace Hindman168

open scoped BigOperators Classical ENNReal

theorem powerUnitPMF_prime_vector {s : ℝ} (hs : 1 < s) (W : ℕ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W) :
    (powerUnitPMF s hs W).map (fun n => fun p : S => n.factorization p) =
      DiscreteProduct.piPMF (fun p : S => primeValuationPMF s hs p (hS p p.property).two_le) := by
  ext a
  rw [powerUnitPMF_prime_vector_product hs W S hS hc a, DiscreteProduct.piPMF_apply]
  apply Finset.prod_congr rfl
  intro p _
  rw [powerUnitPMF_prime_valuation hs W p (hS p p.property) (hc p p.property)]

theorem powerUnitProductPMF_prime_matrix {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs : ∀ i, 1 < s i) (W : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W) :
    (powerUnitProductPMF s hs W).map (fun x i => fun p : S => (x i).factorization p) =
      DiscreteProduct.piPMF (fun i => DiscreteProduct.piPMF
        (fun p : S => primeValuationPMF (s i) (hs i) p (hS p p.property).two_le)) := by
  rw [powerUnitProductPMF, DiscreteProduct.piPMF_map_coordinates
    (fun i => powerUnitPMF (s i) (hs i) W)
    (fun (_ : ι) n => fun p : S => n.factorization p)]
  simp only [powerUnitPMF_prime_vector _ W S hS hc]

theorem powerUnitProductPMF_prime_columns {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs : ∀ i, 1 < s i) (W : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W) :
    (powerUnitProductPMF s hs W).map (fun x => fun p : S => fun i => (x i).factorization p) =
      DiscreteProduct.piPMF (fun p : S => DiscreteProduct.piPMF
        (fun i => primeValuationPMF (s i) (hs i) p (hS p p.property).two_le)) := by
  have h := congrArg (fun μ : PMF (ι → S → ℕ) => μ.map (fun x p i => x i p))
    (powerUnitProductPMF_prime_matrix s hs W S hS hc)
  rw [PMF.map_comp, DiscreteProduct.piPMF_transpose] at h
  exact h

theorem comparisonDivisorPMF_prime_vector {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs : ∀ i, 1 < s i) (W : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W) :
    (comparisonDivisorPMF s hs W).map (fun n => fun p : S => n.factorization p) =
      DiscreteProduct.piPMF (fun p : S => valuationSumPMF s hs p (hS p p.property).two_le) := by
  have hfactor : (powerUnitProductPMF s hs W).map
        (fun x => fun p : S => (∏ i, x i).factorization p) =
      (powerUnitProductPMF s hs W).map
        (fun x => fun p : S => ∑ i, (x i).factorization p) := by
    apply DiscreteProduct.map_congr_support
    intro x hx
    funext p
    exact Nat.factorization_prod_apply
      (fun i _ => ((powerUnitProductPMF_support s hs W x).mp hx i).1)
  have h := congrArg (fun μ : PMF (S → ι → ℕ) => μ.map (fun x p => ∑ i, x p i))
    (powerUnitProductPMF_prime_columns s hs W S hS hc)
  rw [PMF.map_comp, DiscreteProduct.piPMF_map_coordinates
    (fun p : S => DiscreteProduct.piPMF
      (fun i => primeValuationPMF (s i) (hs i) p (hS p p.property).two_le))
    (fun (_ : S) x => ∑ i, x i)] at h
  rw [comparisonDivisorPMF, PMF.map_comp]
  change (powerUnitProductPMF s hs W).map
    (fun x => fun p : S => (∏ i, x i).factorization p) = _
  rw [hfactor]
  exact h

theorem comparisonDivisorPMF_valuation_atom_bound_of_card_le {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs : ∀ i, 1 < s i) (W p b : ℕ) (hp : p.Prime)
    (hc : p.Coprime W) (hb : Fintype.card ι ≤ b) (a : ℕ) :
    (((comparisonDivisorPMF s hs W).map (fun n => n.factorization p)) a).toReal ≤
      ((a + 1 : ℕ) : ℝ) ^ b * ((p : ℝ) ^ a)⁻¹ := by
  apply (comparisonDivisorPMF_valuation_atom_bound s hs W p hp hc a).trans
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))
  exact_mod_cast Nat.pow_le_pow_right (Nat.succ_pos a) hb

end Hindman168
