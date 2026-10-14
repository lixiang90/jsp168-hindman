import Hindman168.PrimePowerCRTExcessTransfer
import Hindman168.ActualDivisorRowCRT
import Hindman168.HarmonicDivisorMass

/-!
# Original divisor-averaged, prime-restricted CRT error

Each divisor draw uses its own original product modulus, including
zero valuation primes. Actual kernel factorization, bounded prime-law
transfer, and the original divisor weights give the absolute restricted
mean-one error. The harmonic specialization uses the proved genuine
global moment, rather than taking that moment bound as a hypothesis.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

abbrev rowCRTModulus {q : ℕ} (S : Finset ℕ) (k : Fin q → ℕ) : ℕ :=
  ∏ p : S, (p : ℕ) ^ (∑ u, (k u).factorization p)

theorem rowCRTModulus_ne_zero {q : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (k : Fin q → ℕ) : rowCRTModulus S k ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  exact pow_ne_zero _ (hS p p.property).ne_zero

noncomputable def rowCRTUniformParameterMass {q : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (k : Fin q → ℕ) (n : ℕ) : Mass (Fin n → ZMod (rowCRTModulus S k)) :=
  letI : NeZero (rowCRTModulus S k) := ⟨rowCRTModulus_ne_zero S hS k⟩
  piMass (fun _ : Fin n => zmodUnitUniformMass (rowCRTModulus S k))

noncomputable def rowCRTBadEvent {q n : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (k : Fin q → ℕ) (D : Finset (MvPolynomial (Fin n) ℤ))
    (x : Fin n → ZMod (rowCRTModulus S k)) (p : S) : Prop :=
  letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
  primePowerCRTBadEvent (fun p : S => (p : ℕ)) (fun p => hS p p.property)
    Subtype.val_injective (fun p => ∑ u, (k u).factorization p) D x p

theorem restricted_actual_divisor_row_crt_error {q d n : ℕ} {α : Type*}
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (k : Fin q → ℕ)
    (hk : ∀ u, k u ≠ 0) (hcover : ∀ u, (k u).primeFactors ⊆ S)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x)
    (stat : α → Fin n → ZMod (rowCRTModulus S k))
    (c : α → Fin q → Fin d → ℤ) (E : α → Prop)
    (hprimitive : ∀ x, E x → ∀ p : S, ∀ u, ∃ j, (c x u j : ZMod (p : ℕ)) ≠ 0)
    (hindependent : ∀ x, E x → ∀ p : S, (∑ u, (k u).factorization p) ≠ 0 →
      ¬ rowCRTBadEvent S hS k D (stat x) p →
      ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
        ![(fun j => (c x u j : ZMod (p : ℕ))), (fun j => (c x v j : ZMod (p : ℕ)))])
    (V : ℕ) (hV : ∀ u, k u ≤ V) :
    0 ≤ expectation μ (fun x => if E x then normalizedDivisorRowCount k (c x) - 1 else 0) ∧
    expectation μ (fun x => if E x then normalizedDivisorRowCount k (c x) - 1 else 0) ≤
      comparisonPrimePowerCRTIntegrand S hS D k + ((V ^ q : ℕ) : ℝ) *
        distance (μ.mapDomain stat) (rowCRTUniformParameterMass S hS k n) := by
  classical
  letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
  letI : NeZero (rowCRTModulus S k) := ⟨rowCRTModulus_ne_zero S hS k⟩
  have h := restricted_primePower_alpha_crt_transfer (fun p : S => (p : ℕ))
    (fun p => hS p p.property) Subtype.val_injective (fun p => ∑ u, (k u).factorization p)
    (fun p u => (k u).factorization p)
    (fun p u => (rowValuation_le_max (fun u => (k u).factorization p) u).trans
      (rowMaxValuation_le_sum (fun u => (k u).factorization p)))
    D μ hμ stat c E hprimitive hindependent V
    (actual_row_primePart_le S hS k (fun u => Nat.pos_of_ne_zero (hk u)) V hV)
  have heq (x : α) : normalizedDivisorRowCount k (c x) =
      ∏ p : S, primePowerLocalAlpha (p : ℕ) q d
        (rowMaxValuation (fun u => (k u).factorization p))
        (fun u => (k u).factorization p)
        (rowValuation_le_max (fun u => (k u).factorization p)) (c x) :=
    actual_normalized_divisor_row_crt S hS k hk hcover (c x)
  simp_rw [heq]
  exact h

theorem averaged_restricted_divisor_crt_error {q d n : ℕ} {α : Type*}
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (ρ : Mass (Fin q → ℕ))
    (hρ : ∀ k, 0 ≤ ρ k) (htρ : total ρ = 1) (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x)
    (D : Finset (MvPolynomial (Fin n) ℤ))
    (stat : ∀ k : Fin q → ℕ, α → Fin n → ZMod (rowCRTModulus S k))
    (c : α → Fin q → Fin d → ℤ) (E : α → Prop) (V : ℕ) (ε : ℝ)
    (hs : ∀ k ∈ ρ.support, ∀ u, k u ≠ 0 ∧ k u ≤ V ∧ (k u).primeFactors ⊆ S)
    (hprimitive : ∀ x, E x → ∀ p : S, ∀ u, ∃ j, (c x u j : ZMod (p : ℕ)) ≠ 0)
    (hindependent : ∀ k ∈ ρ.support, ∀ x, E x → ∀ p : S,
      (∑ u, (k u).factorization p) ≠ 0 → ¬ rowCRTBadEvent S hS k D (stat k x) p →
        ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
          ![(fun j => (c x u j : ZMod (p : ℕ))), (fun j => (c x v j : ZMod (p : ℕ)))])
    (hresidue : ∀ k ∈ ρ.support, distance (μ.mapDomain (stat k)) (rowCRTUniformParameterMass S hS k n) ≤ ε) :
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
    have h := restricted_actual_divisor_row_crt_error S hS k (fun u => (hs k hk u).1)
      (fun u => (hs k hk u).2.2) D μ hμ (stat k) c E hprimitive (hindependent k hk)
      V (fun u => (hs k hk u).2.1)
    exact ⟨h.1, h.2.trans (add_le_add_right
      (mul_le_mul_of_nonneg_left (hresidue k hk) (Nat.cast_nonneg (V ^ q))) _)⟩
  have h0 := expectation_nonneg_support ρ (fun k => f k - event μ E) hρ (fun k hk => (hpoint k hk).1)
  have hle := expectation_mono_support ρ (fun k => f k - event μ E)
    (fun k => comparisonPrimePowerCRTIntegrand S hS D k + ((V ^ q : ℕ) : ℝ) * ε)
    hρ (fun k hk => (hpoint k hk).2)
  rw [expectation_sub, expectation_const, htρ, one_mul] at h0 hle
  rw [expectation_add_const, htρ, one_mul] at hle
  exact ⟨h0, hle⟩

end Hindman168
