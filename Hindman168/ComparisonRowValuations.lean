import Hindman168.ComparisonPrimeIndependence

/-!
# Actual row and prime independence for comparison divisors

Each row is the product of its own independent raw draws. Its original
joint valuation law is identified with the product of the sum-geometric
row laws, and transposition preserves independence across tested primes.
-/

namespace Hindman168

open scoped BigOperators Classical ENNReal

noncomputable def comparisonRowPMF {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ι → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W : ℕ) : PMF (ι → ℕ) :=
  DiscreteProduct.piPMF (fun i => comparisonDivisorPMF (s i) (hs i) W)

theorem comparisonRowPMF_valuation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ι → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ)
    (hp : p.Prime) (hc : p.Coprime W) :
    (comparisonRowPMF s hs W).map (fun x i => (x i).factorization p) =
      DiscreteProduct.piPMF (fun i => valuationSumPMF (s i) (hs i) p hp.two_le) := by
  rw [comparisonRowPMF, DiscreteProduct.piPMF_map_coordinates
    (fun i => comparisonDivisorPMF (s i) (hs i) W)
    (fun (_ : ι) n => n.factorization p)]
  simp only [comparisonDivisorPMF_valuation _ _ W p hp hc]

theorem comparisonRowPMF_prime_matrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ι → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W) :
    (comparisonRowPMF s hs W).map (fun x i => fun p : S => (x i).factorization p) =
      DiscreteProduct.piPMF (fun i => DiscreteProduct.piPMF
        (fun p : S => valuationSumPMF (s i) (hs i) p (hS p p.property).two_le)) := by
  rw [comparisonRowPMF, DiscreteProduct.piPMF_map_coordinates
    (fun i => comparisonDivisorPMF (s i) (hs i) W)
    (fun (_ : ι) n => fun p : S => n.factorization p)]
  simp only [comparisonDivisorPMF_prime_vector _ _ W S hS hc]

theorem comparisonRowPMF_prime_columns {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ι → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W) :
    (comparisonRowPMF s hs W).map (fun x => fun p : S => fun i => (x i).factorization p) =
      DiscreteProduct.piPMF (fun p : S => DiscreteProduct.piPMF
        (fun i => valuationSumPMF (s i) (hs i) p (hS p p.property).two_le)) := by
  have h := congrArg (fun μ : PMF (ι → S → ℕ) => μ.map (fun x p i => x i p))
    (comparisonRowPMF_prime_matrix s hs W S hS hc)
  rw [PMF.map_comp, DiscreteProduct.piPMF_transpose] at h
  exact h

theorem comparisonRowPMF_valuation_atom_bound {q : ℕ} {κ : Type*} [Fintype κ]
    (s : Fin q → κ → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ)
    (hp : p.Prime) (hc : p.Coprime W) (a : Fin q → ℕ) :
    (((comparisonRowPMF s hs W).map (fun x i => (x i).factorization p)) a).toReal ≤
      (∏ i, ((a i + 1 : ℕ) : ℝ) ^ Fintype.card κ) * ((p : ℝ) ^ (∑ i, a i))⁻¹ := by
  rw [comparisonRowPMF_valuation s hs W p hp hc, DiscreteProduct.piPMF_apply,
    ENNReal.toReal_prod]
  calc
    _ ≤ ∏ i, (((a i + 1 : ℕ) : ℝ) ^ Fintype.card κ * ((p : ℝ) ^ a i)⁻¹) :=
      Finset.prod_le_prod (fun _ _ => ENNReal.toReal_nonneg)
        (fun i _ => valuationSumPMF_atom_bound_toReal (s i) (hs i) p hp.two_le (a i))
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      Finset.prod_pow_eq_pow_sum]

end Hindman168
