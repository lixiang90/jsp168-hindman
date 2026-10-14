import Hindman168.MasterPrimeSquarefreeLaw
import Hindman168.AveragedDivisorCRTError

/-!
# Transfer only the mod-prime beta test

The original row kernel still uses its true prime-power divisor moduli.
After pointwise domination, the beta test is transferred at the squarefree
prime product. High prime-power equidistribution of the prime parameters
is unnecessary. Zero row valuations make beta vanish independently of
the polynomial test, so no projection from ZMod 1 is introduced.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem squarefreePrimeModuli_pairwise_coprime (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Pairwise (fun p r : S => (p : ℕ).Coprime (r : ℕ)) := by
  simpa only [pow_one] using primePowerModuli_pairwise_coprime
    (fun p : S => (p : ℕ)) (fun p => hS p p.property) Subtype.val_injective (fun _ => 1)

noncomputable def squarefreeCRTBadEvent {n : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (D : Finset (MvPolynomial (Fin n) ℤ))
    (x : Fin n → ZMod (squarefreeCRTModulus S)) (p : S) : Prop :=
  letI : NeZero (p : ℕ) := ⟨(hS p p.property).ne_zero⟩
  unitPolynomialTestEvent D (p : ℕ) (fun j => ZMod.prodEquivPi
    (fun p : S => (p : ℕ)) (squarefreePrimeModuli_pairwise_coprime S hS) (x j) p)

theorem squarefreeCRTBadEvent_natCast {n : ℕ} (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (x : Fin n → ℕ) (p : S) :
    squarefreeCRTBadEvent S hS D (fun j => (x j : ZMod (squarefreeCRTModulus S))) p ↔
      letI : NeZero (p : ℕ) := ⟨(hS p p.property).ne_zero⟩
      unitPolynomialTestEvent D (p : ℕ) (fun j => (x j : ZMod (p : ℕ))) := by
  simp only [squarefreeCRTBadEvent, ZMod.prodEquivPi_apply, map_natCast]

theorem squarefreeCRT_beta_uniform_expectation {q n : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (D : Finset (MvPolynomial (Fin n) ℤ)) (k : Fin q → ℕ) :
    expectation (squarefreeCRTUniformParameterMass S hS n)
      (localExcessBetaProduct (fun p : S => (p : ℕ))
        (fun p : S => fun u => (k u).factorization p)
        (fun p x => squarefreeCRTBadEvent S hS D x p)) = comparisonPrimePowerCRTIntegrand S hS D k := by
  letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
  letI : NeZero (squarefreeCRTModulus S) := ⟨squarefreeCRTModulus_ne_zero S hS⟩
  let stat := fun (x : Fin n → ZMod (squarefreeCRTModulus S)) (p : S) j =>
    ZMod.prodEquivPi (fun p : S => (p : ℕ)) (squarefreePrimeModuli_pairwise_coprime S hS) (x j) p
  let test := fun x : ∀ p : S, Fin n → ZMod (p : ℕ) =>
    (∏ p : S, (1 + localExcessBeta (p : ℕ) (fun u => (k u).factorization p)
      (unitPolynomialTestEvent D (p : ℕ) (x p)))) - 1
  have h := expectation_push (squarefreeCRTUniformParameterMass S hS n) stat test
  have hm := zmodUnitUniformMass_crt_vector (fun p : S => (p : ℕ))
    (squarefreePrimeModuli_pairwise_coprime S hS) n
  change (squarefreeCRTUniformParameterMass S hS n).mapDomain stat = _ at hm
  rw [hm] at h
  rw [comparisonPrimePowerCRTIntegrand_eq]
  exact h.symm

theorem squarefreeCRT_beta_expectation_transfer {q n : ℕ} {α : Type*}
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (k : Fin q → ℕ)
    (hk : ∀ u, 0 < k u) (D : Finset (MvPolynomial (Fin n) ℤ))
    (V : ℕ) (hV : ∀ u, k u ≤ V) (μ : Mass α)
    (stat : α → Fin n → ZMod (squarefreeCRTModulus S)) :
    |expectation μ (fun x => localExcessBetaProduct (fun p : S => (p : ℕ))
        (fun p : S => fun u => (k u).factorization p)
        (fun p y => squarefreeCRTBadEvent S hS D y p) (stat x)) -
        comparisonPrimePowerCRTIntegrand S hS D k| ≤
      ((V ^ q : ℕ) : ℝ) * distance (μ.mapDomain stat) (squarefreeCRTUniformParameterMass S hS n) := by
  letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
  have h := localExcessBetaProduct_expectation_transfer (fun p : S => (p : ℕ))
    (fun p : S => fun u => (k u).factorization p)
    (fun p y => squarefreeCRTBadEvent S hS D y p) V (actual_row_primePart_le S hS k hk V hV)
    (μ.mapDomain stat) (squarefreeCRTUniformParameterMass S hS n)
  rw [expectation_push, squarefreeCRT_beta_uniform_expectation] at h
  exact h

theorem restricted_actual_divisor_row_squarefree_error {q d n : ℕ} {α : Type*}
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (k : Fin q → ℕ)
    (hk : ∀ u, k u ≠ 0) (hcover : ∀ u, (k u).primeFactors ⊆ S)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x)
    (stat : α → Fin n → ZMod (squarefreeCRTModulus S))
    (c : α → Fin q → Fin d → ℤ) (E : α → Prop)
    (hprimitive : ∀ x, E x → ∀ p : S, ∀ u, ∃ j, (c x u j : ZMod (p : ℕ)) ≠ 0)
    (hindependent : ∀ x, E x → ∀ p : S, (∑ u, (k u).factorization p) ≠ 0 →
      ¬ squarefreeCRTBadEvent S hS D (stat x) p →
      ∀ u v, u ≠ v → LinearIndependent (ZMod (p : ℕ))
        ![(fun j => (c x u j : ZMod (p : ℕ))), (fun j => (c x v j : ZMod (p : ℕ)))])
    (V : ℕ) (hV : ∀ u, k u ≤ V) :
    0 ≤ expectation μ (fun x => if E x then normalizedDivisorRowCount k (c x) - 1 else 0) ∧
    expectation μ (fun x => if E x then normalizedDivisorRowCount k (c x) - 1 else 0) ≤
      comparisonPrimePowerCRTIntegrand S hS D k + ((V ^ q : ℕ) : ℝ) *
        distance (μ.mapDomain stat) (squarefreeCRTUniformParameterMass S hS n) := by
  letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
  let f := fun x => if E x then normalizedDivisorRowCount k (c x) - 1 else 0
  let g := fun x => localExcessBetaProduct (fun p : S => (p : ℕ))
    (fun p : S => fun u => (k u).factorization p)
    (fun p y => squarefreeCRTBadEvent S hS D y p) (stat x)
  have hpoint (x : α) : 0 ≤ f x ∧ f x ≤ g x := by
    dsimp only [f, g, localExcessBetaProduct]
    rw [actual_normalized_divisor_row_crt S hS k hk hcover]
    apply prod_excess_indicator_domination
    · intro p
      exact (primePowerLocalAlpha_bounds (p : ℕ) q d _ _ (rowValuation_le_max _) (c x)).1
    · intro p
      exact localExcessBeta_nonneg (p : ℕ) _ _
    · intro hx p
      exact (primePowerLocalAlpha_excess_le_beta_active (p : ℕ) q d _
        (∑ u, (k u).factorization p) (hS p p.property) _ (rowValuation_le_max _)
        (fun u => (rowValuation_le_max _ u).trans (rowMaxValuation_le_sum _))
        (c x) _ (hprimitive x hx p) (hindependent x hx p)).2
  have h0 := expectation_nonneg μ f hμ (fun x => (hpoint x).1)
  have hdom := expectation_mono μ f g hμ (fun x => (hpoint x).2)
  have htrans := squarefreeCRT_beta_expectation_transfer S hS k
    (fun u => Nat.pos_of_ne_zero (hk u)) D V hV μ stat
  have hle := (le_abs_self (expectation μ g - comparisonPrimePowerCRTIntegrand S hS D k)).trans htrans
  exact ⟨h0, by linarith⟩

end Hindman168
