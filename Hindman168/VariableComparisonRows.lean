import Hindman168.ComparisonRowValuations
import Hindman168.LocalExcessValuationWeights

/-!
# Actual comparison rows with different raw index families

Every row is the product of its own independent raw draws. Coordinate
pushforward and transposition give the original independent valuation
columns. A common bound on the raw cardinalities gives the same valuation
weight majorant as in the finite-cell moment proof, without padding draws.
-/

namespace Hindman168

open scoped BigOperators Classical ENNReal

noncomputable def variableComparisonRowPMF {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j) (W : ℕ) : PMF (ι → ℕ) :=
  DiscreteProduct.piPMF (fun i => comparisonDivisorPMF (s i) (hs i) W)

theorem variableComparisonRowPMF_valuation {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j) (W p : ℕ)
    (hp : p.Prime) (hc : p.Coprime W) :
    (variableComparisonRowPMF s hs W).map (fun x i => (x i).factorization p) =
      DiscreteProduct.piPMF (fun i => valuationSumPMF (s i) (hs i) p hp.two_le) := by
  rw [variableComparisonRowPMF, DiscreteProduct.piPMF_map_coordinates
    (fun i => comparisonDivisorPMF (s i) (hs i) W) (fun (_ : ι) n => n.factorization p)]
  simp only [comparisonDivisorPMF_valuation _ _ W p hp hc]

theorem variableComparisonRowPMF_prime_matrix {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j) (W : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W) :
    (variableComparisonRowPMF s hs W).map (fun x i => fun p : S => (x i).factorization p) =
      DiscreteProduct.piPMF (fun i => DiscreteProduct.piPMF
        (fun p : S => valuationSumPMF (s i) (hs i) p (hS p p.property).two_le)) := by
  rw [variableComparisonRowPMF, DiscreteProduct.piPMF_map_coordinates
    (fun i => comparisonDivisorPMF (s i) (hs i) W) (fun (_ : ι) n => fun p : S => n.factorization p)]
  simp only [comparisonDivisorPMF_prime_vector _ _ W S hS hc]

theorem variableComparisonRowPMF_prime_columns {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j) (W : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hc : ∀ p ∈ S, p.Coprime W) :
    (variableComparisonRowPMF s hs W).map (fun x => fun p : S => fun i => (x i).factorization p) =
      DiscreteProduct.piPMF (fun p : S => DiscreteProduct.piPMF
        (fun i => valuationSumPMF (s i) (hs i) p (hS p p.property).two_le)) := by
  have h := congrArg (fun μ : PMF (ι → S → ℕ) => μ.map (fun x p i => x i p))
    (variableComparisonRowPMF_prime_matrix s hs W S hS hc)
  rw [PMF.map_comp, DiscreteProduct.piPMF_transpose] at h
  exact h

theorem variableComparisonRowPMF_valuation_atom_bound {q : ℕ}
    {κ : Fin q → Type*} [∀ i, Fintype (κ i)]
    (s : ∀ i, κ i → ℝ) (hs : ∀ i j, 1 < s i j) (W p b : ℕ)
    (hp : p.Prime) (hc : p.Coprime W) (hb : ∀ i, Fintype.card (κ i) ≤ b) (a : Fin q → ℕ) :
    (((variableComparisonRowPMF s hs W).map (fun x i => (x i).factorization p)) a).toReal ≤
      rowValuationWeight p b a := by
  rw [variableComparisonRowPMF_valuation s hs W p hp hc, DiscreteProduct.piPMF_apply,
    ENNReal.toReal_prod]
  have hrow (i : Fin q) : (valuationSumPMF (s i) (hs i) p hp.two_le (a i)).toReal ≤
      ((a i + 1 : ℕ) : ℝ) ^ b * ((p : ℝ) ^ a i)⁻¹ := by
    have h := comparisonDivisorPMF_valuation_atom_bound_of_card_le (s i) (hs i) W p b hp hc (hb i) (a i)
    rwa [comparisonDivisorPMF_valuation (s i) (hs i) W p hp hc] at h
  calc
    _ ≤ ∏ i, (((a i + 1 : ℕ) : ℝ) ^ b * ((p : ℝ) ^ a i)⁻¹) :=
      Finset.prod_le_prod (fun _ _ => ENNReal.toReal_nonneg) (fun i _ => hrow i)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      Finset.prod_pow_eq_pow_sum]; rfl

end Hindman168
