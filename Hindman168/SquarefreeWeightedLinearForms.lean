import Hindman168.SquarefreeExcessTransfer
import Hindman168.VariableWeightedLinearForms

/-!
# Complete weighted integer estimate with only squarefree prime-law error

The base law retains its original product-of-divisors modulus. Only the
prime-parameter beta test uses the squarefree modulus. The actual finite
harmonic moment, restrictions and varying row arities are unchanged.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem averaged_restricted_divisor_squarefree_error {q d n : ℕ} {α : Type*}
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (ρ : Mass (Fin q → ℕ))
    (hρ : ∀ k, 0 ≤ ρ k) (htρ : total ρ = 1) (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x)
    (D : Finset (MvPolynomial (Fin n) ℤ))
    (stat : α → Fin n → ZMod (squarefreeCRTModulus S))
    (c : α → Fin q → Fin d → ℤ) (E : α → Prop) (V : ℕ) (ε : ℝ)
    (hs : ∀ k ∈ ρ.support, ∀ u, k u ≠ 0 ∧ k u ≤ V ∧ (k u).primeFactors ⊆ S)
    (hprimitive : ∀ x, E x → ∀ p : S, ∀ u, ∃ j, (c x u j : ZMod (p : ℕ)) ≠ 0)
    (hindependent : ∀ k ∈ ρ.support, ∀ x, E x → ∀ p : S,
      (∑ u, (k u).factorization p) ≠ 0 → ¬ squarefreeCRTBadEvent S hS D (stat x) p →
        ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
          ![(fun j => (c x u j : ZMod (p : ℕ))), (fun j => (c x v j : ZMod (p : ℕ)))])
    (hresidue : distance (μ.mapDomain stat) (squarefreeCRTUniformParameterMass S hS n) ≤ ε) :
    0 ≤ expectation ρ (fun k => expectation μ (fun x => if E x then normalizedDivisorRowCount k (c x) else 0)) -
      event μ E ∧
    expectation ρ (fun k => expectation μ (fun x => if E x then normalizedDivisorRowCount k (c x) else 0)) -
      event μ E ≤ expectation ρ (comparisonPrimePowerCRTIntegrand S hS D) + ((V ^ q : ℕ) : ℝ) * ε := by
  let f := fun k => expectation μ (fun x => if E x then normalizedDivisorRowCount k (c x) else 0)
  have hpoint (k : Fin q → ℕ) (hk : k ∈ ρ.support) :
      0 ≤ f k - event μ E ∧ f k - event μ E ≤
        comparisonPrimePowerCRTIntegrand S hS D k + ((V ^ q : ℕ) : ℝ) * ε := by
    rw [show f k - event μ E = expectation μ
      (fun x => if E x then normalizedDivisorRowCount k (c x) - 1 else 0) from
        restricted_expectation_sub_event μ E _]
    have h := restricted_actual_divisor_row_squarefree_error S hS k (fun u => (hs k hk u).1)
      (fun u => (hs k hk u).2.2) D μ hμ stat c E hprimitive (hindependent k hk)
      V (fun u => (hs k hk u).2.1)
    exact ⟨h.1, h.2.trans (add_le_add_right
      (mul_le_mul_of_nonneg_left hresidue (Nat.cast_nonneg (V ^ q))) _)⟩
  have h0 := expectation_nonneg_support ρ (fun k => f k - event μ E) hρ (fun k hk => (hpoint k hk).1)
  have hle := expectation_mono_support ρ (fun k => f k - event μ E)
    (fun k => comparisonPrimePowerCRTIntegrand S hS D k + ((V ^ q : ℕ) : ℝ) * ε)
    hρ (fun k hk => (hpoint k hk).2)
  rw [expectation_sub, expectation_const, htρ, one_mul] at h0 hle
  rw [expectation_add_const, htρ, one_mul] at hle
  exact ⟨h0, hle⟩

theorem squarefree_weighted_integer_linear_forms_mean_one_error {q d n : ℕ} {α : Type*}
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (ρ : Fin q → Mass ℕ)
    (hρ : ∀ u k, 0 ≤ ρ u k) (htρ : ∀ u, total (ρ u) = 1)
    (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x) (htμ : total μ = 1)
    (base : α → Mass (Fin d → ℤ)) (c : α → Fin q → Fin d → ℤ) (E : α → Prop)
    (D : Finset (MvPolynomial (Fin n) ℤ))
    (stat : α → Fin n → ZMod (squarefreeCRTModulus S))
    (V : ℕ) (εbase εprime : ℝ) (hεbase : 0 ≤ εbase)
    (hs : ∀ k ∈ (piMass ρ).support, ∀ u, k u ≠ 0 ∧ k u ≤ V ∧ (k u).primeFactors ⊆ S)
    (hprimitive : ∀ x, E x → ∀ p : S, ∀ u, ∃ j, (c x u j : ZMod (p : ℕ)) ≠ 0)
    (hindependent : ∀ k ∈ (piMass ρ).support, ∀ x, E x → ∀ p : S,
      (∑ u, (k u).factorization p) ≠ 0 → ¬ squarefreeCRTBadEvent S hS D (stat x) p →
        ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
          ![(fun j => (c x u j : ZMod (p : ℕ))), (fun j => (c x v j : ZMod (p : ℕ)))])
    (hprime : distance (μ.mapDomain stat) (squarefreeCRTUniformParameterMass S hS n) ≤ εprime)
    (hbase : ∀ x, E x → ∀ k, (hk : k ∈ (piMass ρ).support) →
      letI : NeZero (∏ u, k u) := ⟨Finset.prod_ne_zero_iff.mpr (fun u _ => (hs k hk u).1)⟩
      distance ((base x).mapDomain (fun y j => (y j : ZMod (∏ u, k u))))
        (uniformFintypeMass (Fin d → ZMod (∏ u, k u))) ≤ εbase) :
    |expectation μ (fun x => if E x then expectation (base x)
        (fun y => ∏ u, integerDivisorMask (ρ u) (∑ j, c x u j * y j)) else 0) - event μ E| ≤
      expectation (piMass ρ) (comparisonPrimePowerCRTIntegrand S hS D) +
        ((V ^ q : ℕ) : ℝ) * (εbase + εprime) := by
  let f := fun x => if E x then expectation (base x)
    (fun y => ∏ u, integerDivisorMask (ρ u) (∑ j, c x u j * y j)) else 0
  let g := fun x => if E x then expectation (piMass ρ)
    (fun k => normalizedDivisorRowCount k (c x)) else 0
  let A := expectation (piMass ρ) (fun k => expectation μ
    (fun x => if E x then normalizedDivisorRowCount k (c x) else 0))
  have hgpoint (x : α) : g x = expectation (piMass ρ)
      (fun k => if E x then normalizedDivisorRowCount k (c x) else 0) := by
    by_cases hx : E x
    · simp only [g, if_pos hx]
    · simp only [g, if_neg hx, expectation, mul_zero, Finsupp.sum_fun_zero]
  have hg : expectation μ g = A := by
    rw [show g = (fun x => expectation (piMass ρ)
      (fun k => if E x then normalizedDivisorRowCount k (c x) else 0)) from funext hgpoint]
    exact expectation_comm μ (piMass ρ) _
  have hpoint (x : α) : |f x - g x| ≤ ((V ^ q : ℕ) : ℝ) * εbase := by
    by_cases hx : E x
    · simp only [f, g, if_pos hx]
      exact weighted_integer_masks_base_error ρ hρ htρ (base x) (c x) V εbase hεbase
        (fun k hk u => ⟨(hs k hk u).1, (hs k hk u).2.1⟩) (hbase x hx)
    · simp only [f, g, if_neg hx, sub_self, abs_zero]
      exact mul_nonneg (Nat.cast_nonneg _) hεbase
  have hb := expectation_difference_support_bound μ hμ f g (((V ^ q : ℕ) : ℝ) * εbase)
    (fun x _ => hpoint x)
  rw [htμ, one_mul, hg] at hb
  have ha := averaged_restricted_divisor_squarefree_error S hS (piMass ρ) (piMass_nonneg ρ hρ)
    (piMass_total_one ρ htρ) μ hμ D stat c E V εprime hs hprimitive hindependent hprime
  have hac : |A - event μ E| ≤ expectation (piMass ρ) (comparisonPrimePowerCRTIntegrand S hS D) +
      ((V ^ q : ℕ) : ℝ) * εprime := by
    rw [abs_of_nonneg ha.1]
    exact ha.2
  calc
    |expectation μ f - event μ E| = |(expectation μ f - A) + (A - event μ E)| := by congr 1; ring
    _ ≤ |expectation μ f - A| + |A - event μ E| := abs_add_le _ _
    _ ≤ ((V ^ q : ℕ) : ℝ) * εbase +
        (expectation (piMass ρ) (comparisonPrimePowerCRTIntegrand S hS D) + ((V ^ q : ℕ) : ℝ) * εprime) :=
      add_le_add hb hac
    _ = _ := by ring

theorem squarefree_variable_harmonic_integer_linear_forms_mean_one_error {q d n : ℕ} {α : Type*} {κ : Fin q → Type*} [∀ i, Fintype (κ i)]
    (X : ∀ i, κ i → ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hX : ∀ i j, 2 ≤ X i j) (hW : ∀ i j, (∏ p ∈ P, p) ≤ X i j)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) (∏ p ∈ P, p))
    (hlog : ∀ i j, 2 ≤ Real.log (X i j : ℝ))
    (hZ : ∀ i j, powerUnitNormalizer (comparisonExponent (X i j)) 1 ≤ 2 * Real.log (X i j : ℝ))
    (b : ℕ) (hb : ∀ i, Fintype.card (κ i) ≤ b) (w : ℕ) (hw : 0 < w) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hc : ∀ p ∈ S, p.Coprime (∏ p ∈ P, p)) (hgreater : ∀ p ∈ S, w < p)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (hcut : D.sup integerPolynomialCoeffSize ≤ w)
    (hsmall : localExcessPrimeTestConstant (b) q D ≤ (w : ℝ))
    (V : ℕ) (hbound : ∀ i, (∏ j, (X i j) ^ 2) ≤ V)
    (hcover : ∀ m, 0 < m → m ≤ V → m.Coprime (∏ p ∈ P, p) → m.primeFactors ⊆ S)
    (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x) (htμ : total μ = 1)
    (base : α → Mass (Fin d → ℤ)) (c : α → Fin q → Fin d → ℤ) (E : α → Prop)
    (stat : α → Fin n → ZMod (squarefreeCRTModulus S))
    (εbase εprime : ℝ) (hεbase : 0 ≤ εbase)
    (hprimitive : ∀ x, E x → ∀ p : S, ∀ u, ∃ j, (c x u j : ZMod (p : ℕ)) ≠ 0)
    (hindependent : ∀ k ∈ (variableHarmonicRowDivisorMass X (∏ p ∈ P, p)).support,
      ∀ x, E x → ∀ p : S, (∑ u, (k u).factorization p) ≠ 0 →
        ¬ squarefreeCRTBadEvent S hS D (stat x) p →
        ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
          ![(fun j => (c x u j : ZMod (p : ℕ))), (fun j => (c x v j : ZMod (p : ℕ)))])
    (hprime : distance (μ.mapDomain stat) (squarefreeCRTUniformParameterMass S hS n) ≤ εprime)
    (hbase : ∀ x, E x → ∀ k, (hk : k ∈ (variableHarmonicRowDivisorMass X (∏ p ∈ P, p)).support) →
      letI : NeZero (∏ u, k u) := ⟨Finset.prod_ne_zero_iff.mpr
        (fun u _ => (variableHarmonicRowDivisorMass_support X (∏ p ∈ P, p) hX hk u).1.ne')⟩
      distance ((base x).mapDomain (fun y j => (y j : ZMod (∏ u, k u))))
        (uniformFintypeMass (Fin d → ZMod (∏ u, k u))) ≤ εbase) :
    |expectation μ (fun x => if E x then expectation (base x)
        (fun y => ∏ u, integerDivisorMask (harmonicDivisorMass (X u) (∏ p ∈ P, p))
          (∑ j, c x u j * y j)) else 0) - event μ E| ≤
      (4 * Real.exp 3) ^ (∑ i, Fintype.card (κ i)) *
        (2 * localExcessPrimeTestConstant (b) q D / (w : ℝ)) +
          ((V ^ q : ℕ) : ℝ) * (εbase + εprime) := by
  have hs (k : Fin q → ℕ) (hk : k ∈ (variableHarmonicRowDivisorMass X (∏ p ∈ P, p)).support) (u : Fin q) :
      k u ≠ 0 ∧ k u ≤ V ∧ (k u).primeFactors ⊆ S := by
    have hu := variableHarmonicRowDivisorMass_support X (∏ p ∈ P, p) hX hk u
    have hb := hu.2.1.trans (hbound u)
    exact ⟨hu.1.ne', hb, hcover (k u) hu.1 hb hu.2.2⟩
  have h := squarefree_weighted_integer_linear_forms_mean_one_error S hS
    (fun u => harmonicDivisorMass (X u) (∏ p ∈ P, p))
    (fun u => harmonicDivisorMass_nonneg (X u) (∏ p ∈ P, p) (hH u))
    (fun u => harmonicDivisorMass_total (X u) (∏ p ∈ P, p) (hH u))
    μ hμ htμ base c E D stat V εbase εprime hεbase hs hprimitive hindependent hprime hbase
  have hm := variableHarmonicRow_CRT_excess_expectation_bound X P hP hX hW hH hlog hZ
    b w hb hw S hS hc hgreater D hD hcut hsmall
  rw [← variableHarmonicRowDivisorMass_expectation X (∏ p ∈ P, p) hH] at hm
  exact h.trans (add_le_add_left hm _)



end Hindman168
