import Hindman168.AveragedDivisorCRTError
import Hindman168.WeightedMasksBaseTransfer

/-!
# Complete finite weighted integer linear-forms error

Actual independent divisor masks are expanded, the original base residue
law is transferred at the original divisor product, and the genuine CRT
kernel excess is averaged after the original prime-law transfer. Every
prime-only event retains its original probability mass. The harmonic
specialization derives the full O(1/w) moment from the actual raw draws.

The harmonic specialization currently has one common finite raw index
type per row. Varying row arities and the master-family occurrence maps
are separate remaining obligations, as is the asymptotic application.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem weighted_integer_linear_forms_mean_one_error {q d n : ℕ} {α : Type*}
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (ρ : Fin q → Mass ℕ)
    (hρ : ∀ u k, 0 ≤ ρ u k) (htρ : ∀ u, total (ρ u) = 1)
    (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x) (htμ : total μ = 1)
    (base : α → Mass (Fin d → ℤ)) (c : α → Fin q → Fin d → ℤ) (E : α → Prop)
    (D : Finset (MvPolynomial (Fin n) ℤ))
    (stat : ∀ k : Fin q → ℕ, α → Fin n → ZMod (rowCRTModulus S k))
    (V : ℕ) (εbase εprime : ℝ) (hεbase : 0 ≤ εbase)
    (hs : ∀ k ∈ (piMass ρ).support, ∀ u, k u ≠ 0 ∧ k u ≤ V ∧ (k u).primeFactors ⊆ S)
    (hprimitive : ∀ x, E x → ∀ p : S, ∀ u, ∃ j, (c x u j : ZMod (p : ℕ)) ≠ 0)
    (hindependent : ∀ k ∈ (piMass ρ).support, ∀ x, E x → ∀ p : S,
      (∑ u, (k u).factorization p) ≠ 0 → ¬ rowCRTBadEvent S hS k D (stat k x) p →
        ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
          ![(fun j => (c x u j : ZMod (p : ℕ))), (fun j => (c x v j : ZMod (p : ℕ)))])
    (hprime : ∀ k ∈ (piMass ρ).support,
      distance (μ.mapDomain (stat k)) (rowCRTUniformParameterMass S hS k n) ≤ εprime)
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
  have ha := averaged_restricted_divisor_crt_error S hS (piMass ρ) (piMass_nonneg ρ hρ)
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

theorem harmonic_integer_linear_forms_mean_one_error {q d n : ℕ} {α κ : Type*} [Fintype κ]
    (X : Fin q → κ → ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hX : ∀ i j, 2 ≤ X i j) (hW : ∀ i j, (∏ p ∈ P, p) ≤ X i j)
    (hH : ∀ i j, 0 < harmonicNormalizer (X i j) (∏ p ∈ P, p))
    (hlog : ∀ i j, 2 ≤ Real.log (X i j : ℝ))
    (hZ : ∀ i j, powerUnitNormalizer (comparisonExponent (X i j)) 1 ≤ 2 * Real.log (X i j : ℝ))
    (w : ℕ) (hw : 0 < w) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hc : ∀ p ∈ S, p.Coprime (∏ p ∈ P, p)) (hgreater : ∀ p ∈ S, w < p)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
    (hcut : D.sup integerPolynomialCoeffSize ≤ w)
    (hsmall : localExcessPrimeTestConstant (Fintype.card κ) q D ≤ (w : ℝ))
    (V : ℕ) (hbound : ∀ i, (∏ j, (X i j) ^ 2) ≤ V)
    (hcover : ∀ m, 0 < m → m ≤ V → m.Coprime (∏ p ∈ P, p) → m.primeFactors ⊆ S)
    (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x) (htμ : total μ = 1)
    (base : α → Mass (Fin d → ℤ)) (c : α → Fin q → Fin d → ℤ) (E : α → Prop)
    (stat : ∀ k : Fin q → ℕ, α → Fin n → ZMod (rowCRTModulus S k))
    (εbase εprime : ℝ) (hεbase : 0 ≤ εbase)
    (hprimitive : ∀ x, E x → ∀ p : S, ∀ u, ∃ j, (c x u j : ZMod (p : ℕ)) ≠ 0)
    (hindependent : ∀ k ∈ (harmonicRowDivisorMass X (∏ p ∈ P, p)).support,
      ∀ x, E x → ∀ p : S, (∑ u, (k u).factorization p) ≠ 0 →
        ¬ rowCRTBadEvent S hS k D (stat k x) p →
        ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
          ![(fun j => (c x u j : ZMod (p : ℕ))), (fun j => (c x v j : ZMod (p : ℕ)))])
    (hprime : ∀ k ∈ (harmonicRowDivisorMass X (∏ p ∈ P, p)).support,
      distance (μ.mapDomain (stat k)) (rowCRTUniformParameterMass S hS k n) ≤ εprime)
    (hbase : ∀ x, E x → ∀ k, (hk : k ∈ (harmonicRowDivisorMass X (∏ p ∈ P, p)).support) →
      letI : NeZero (∏ u, k u) := ⟨Finset.prod_ne_zero_iff.mpr
        (fun u _ => (harmonicRowDivisorMass_support X (∏ p ∈ P, p) hX hk u).1.ne')⟩
      distance ((base x).mapDomain (fun y j => (y j : ZMod (∏ u, k u))))
        (uniformFintypeMass (Fin d → ZMod (∏ u, k u))) ≤ εbase) :
    |expectation μ (fun x => if E x then expectation (base x)
        (fun y => ∏ u, integerDivisorMask (harmonicDivisorMass (X u) (∏ p ∈ P, p))
          (∑ j, c x u j * y j)) else 0) - event μ E| ≤
      (4 * Real.exp 3) ^ (Fintype.card κ * q) *
        (2 * localExcessPrimeTestConstant (Fintype.card κ) q D / (w : ℝ)) +
          ((V ^ q : ℕ) : ℝ) * (εbase + εprime) := by
  have hs (k : Fin q → ℕ) (hk : k ∈ (harmonicRowDivisorMass X (∏ p ∈ P, p)).support) (u : Fin q) :
      k u ≠ 0 ∧ k u ≤ V ∧ (k u).primeFactors ⊆ S := by
    have hu := harmonicRowDivisorMass_support X (∏ p ∈ P, p) hX hk u
    have hb := hu.2.1.trans (hbound u)
    exact ⟨hu.1.ne', hb, hcover (k u) hu.1 hb hu.2.2⟩
  have h := weighted_integer_linear_forms_mean_one_error S hS
    (fun u => harmonicDivisorMass (X u) (∏ p ∈ P, p))
    (fun u => harmonicDivisorMass_nonneg (X u) (∏ p ∈ P, p) (hH u))
    (fun u => harmonicDivisorMass_total (X u) (∏ p ∈ P, p) (hH u))
    μ hμ htμ base c E D stat V εbase εprime hεbase hs hprimitive hindependent hprime hbase
  have hm := harmonicRow_CRT_excess_expectation_bound X P hP hX hW hH hlog hZ
    w hw S hS hc hgreater D hD hcut hsmall
  rw [← harmonicRowDivisorMass_expectation X (∏ p ∈ P, p) hH] at hm
  exact h.trans (add_le_add_left hm _)

end Hindman168
