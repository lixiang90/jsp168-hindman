import Hindman168.JSP000168

/-!
Endpoint checks for the final proof chain. This file adds no mathematical premise.
Successful compilation, axiom inspection and fresh kernel replay must be
recorded separately before treating the final proof chain as verified.
-/

open scoped BigOperators

set_option pp.universes true
set_option pp.explicit true

-- Every key exported theorem from the four new library modules.
#check @Hindman168.originalIntervalAdapter_lipschitz_star
#check @Hindman168.native_periodic_interval_inverse_of_original_niltests
#check @Hindman168.original_interval_niltest_inverse_from_openai
#check @Hindman168.native_periodic_interval_inverse_from_openai
#check @Hindman168.native_periodic_interval_inverse_family_from_openai
#check @Hindman168.strongConjecture_from_openai
#check @Hindman168.jsp000168_from_openai

#print axioms Hindman168.originalIntervalAdapter_lipschitz_star
#print axioms Hindman168.native_periodic_interval_inverse_of_original_niltests
#print axioms Hindman168.original_interval_niltest_inverse_from_openai
#print axioms Hindman168.native_periodic_interval_inverse_from_openai
#print axioms Hindman168.native_periodic_interval_inverse_family_from_openai
#print axioms Hindman168.strongConjecture_from_openai
#print axioms Hindman168.jsp000168_from_openai

#print Hindman168.StrongConjecture
#print Hindman168.StrongWitness

-- Its implicit proposition is inferred from the complete theorem type.
-- Unlike applying a theorem to inferred arguments, this retains every binder.
private def endpointProposition {P : Prop} (_proof : P) : Prop := P

example : endpointProposition (@Hindman168.jsp000168_from_openai) =
    (∀ (r : ℕ) (χ : ℕ → Fin r) (m : ℕ),
      ∃ (A : Finset ℕ) (c : Fin r),
        A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
          ∀ B : Finset ℕ, B ⊆ A → B.Nonempty →
            χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c) := rfl

example : endpointProposition
    (@Hindman168.native_periodic_interval_inverse_family_from_openai) =
    (∀ (t : ℕ), 2 ≤ t →
      Hindman168.HasNativePeriodicIntervalInverse.{0} (t - 1) t) := rfl

-- Both named propositions are reduced. In particular, there is no remaining
-- inverse-family argument, alignment oracle, section variable or typeclass binder.
example : endpointProposition (@Hindman168.strongConjecture_from_openai) =
    (∀ (r : ℕ) (χ : ℕ → Fin r) (m : ℕ) (R D : ℝ),
      2 ≤ R → 1 ≤ D →
      ∃ a : Fin m → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
        (∀ i, R *
          ((∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i), (a j : ℝ)) +
           (∏ j ∈ Finset.univ.filter (fun j : Fin m => j < i), (a j : ℝ))) ^ D <
          (a i : ℝ)) ∧
        ∃ c : Fin r, ∀ S : Finset (Fin m), S.Nonempty →
          χ (∑ i ∈ S, a i) = c ∧ χ (∏ i ∈ S, a i) = c) := rfl
