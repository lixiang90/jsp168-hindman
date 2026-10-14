import Hindman168.CountableValuationSums
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Valuation masses of actual products of comparison raw draws

The original independent W-unit draws are mapped to their actual natural
product. Positivity on their support makes factorization additive, so its
valuation law is the constructed sum of the actual geometric marginals.
-/

namespace Hindman168

open scoped BigOperators Classical ENNReal

noncomputable def powerUnitProductPMF {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs : ∀ i, 1 < s i) (W : ℕ) : PMF (ι → ℕ) :=
  DiscreteProduct.piPMF (fun i => powerUnitPMF (s i) (hs i) W)

noncomputable def comparisonDivisorPMF {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs : ∀ i, 1 < s i) (W : ℕ) : PMF ℕ :=
  (powerUnitProductPMF s hs W).map (fun x => ∏ i, x i)

theorem powerUnitProductPMF_support {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs : ∀ i, 1 < s i) (W : ℕ) (x : ι → ℕ) :
    x ∈ (powerUnitProductPMF s hs W).support ↔ ∀ i, x i ≠ 0 ∧ (x i).Coprime W := by
  rw [powerUnitProductPMF, DiscreteProduct.piPMF_mem_support]
  simp only [powerUnitPMF_support, Set.mem_setOf_eq]

theorem powerUnitProductPMF_valuation_coordinates {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs : ∀ i, 1 < s i) (W p : ℕ) (hp : p.Prime) (hc : p.Coprime W) :
    (powerUnitProductPMF s hs W).map (fun x i => (x i).factorization p) =
      DiscreteProduct.piPMF (fun i => primeValuationPMF (s i) (hs i) p hp.two_le) := by
  rw [powerUnitProductPMF, DiscreteProduct.piPMF_map_coordinates
    (fun i => powerUnitPMF (s i) (hs i) W) (fun (_ : ι) n => n.factorization p)]
  simp only [powerUnitPMF_prime_valuation _ W p hp hc]

theorem comparisonDivisorPMF_valuation {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs : ∀ i, 1 < s i) (W p : ℕ) (hp : p.Prime) (hc : p.Coprime W) :
    (comparisonDivisorPMF s hs W).map (fun n => n.factorization p) =
      valuationSumPMF s hs p hp.two_le := by
  have hsum : (powerUnitProductPMF s hs W).map (fun x => (∏ i, x i).factorization p) =
      (powerUnitProductPMF s hs W).map (fun x => ∑ i, (x i).factorization p) := by
    apply DiscreteProduct.map_congr_support
    intro x hx
    exact Nat.factorization_prod_apply
      (fun i _ => ((powerUnitProductPMF_support s hs W x).mp hx i).1)
  rw [comparisonDivisorPMF, PMF.map_comp]
  change (powerUnitProductPMF s hs W).map (fun x => (∏ i, x i).factorization p) = _
  rw [hsum]
  have h := congrArg (fun μ : PMF (ι → ℕ) => μ.map (fun x => ∑ i, x i))
    (powerUnitProductPMF_valuation_coordinates s hs W p hp hc)
  rw [PMF.map_comp] at h
  exact h

theorem comparisonDivisorPMF_valuation_atom_bound {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs : ∀ i, 1 < s i) (W p : ℕ) (hp : p.Prime)
    (hc : p.Coprime W) (a : ℕ) :
    (((comparisonDivisorPMF s hs W).map (fun n => n.factorization p)) a).toReal ≤
      ((a + 1 : ℕ) : ℝ) ^ Fintype.card ι * ((p : ℝ) ^ a)⁻¹ := by
  rw [comparisonDivisorPMF_valuation s hs W p hp hc]
  exact valuationSumPMF_atom_bound_toReal s hs p hp.two_le a

end Hindman168
