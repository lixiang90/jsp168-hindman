import Hindman168.DyadicMainCoprimality

/-!
# Full induction for dyadic rough coprimality

Induction is on the total number of coordinates, including coordinates
on which a polynomial may not depend. Removing the main coordinate always
decreases that number, and the formal main-leading polynomial is nonzero.
The finitely many variable permutations are controlled before any varying
endpoint arrays are selected, so all constants are endpoint-independent.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem dyadicCoprimeControl_of_main_permutations {m n w0 e0 K : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ)
    (h : ∀ (s : Equiv.Perm (Fin (m + 1))) (t : Equiv.Perm (Fin (n + 1))),
      DyadicMainCoprimeControl (MvPolynomial.rename s.symm F)
        (MvPolynomial.rename t.symm G) w0 e0 K) :
    DyadicCoprimeControl F G w0 e0 K := by
  intro eF eG heF heG w L hww hw hL hLF hLG
  obtain ⟨s, hs⟩ := exists_largest_dyadic_main_permutation eF
  obtain ⟨t, ht⟩ := exists_largest_dyadic_main_permutation eG
  have hp := h s t (fun i => eF (s i)) (fun i => eG (t i))
    (fun i => heF (s i)) (fun i => heG (t i)) hs ht w L hww hw hL
    (fun i => hLF (s i)) (fun i => hLG (t i))
  rw [dyadicCommonPrimeMass_reindex eF eG s t F G] at hp
  exact hp

theorem exists_dyadic_control_of_main_permutations {m n : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℤ) (G : MvPolynomial (Fin (n + 1)) ℤ)
    (h : ∀ (s : Equiv.Perm (Fin (m + 1))) (t : Equiv.Perm (Fin (n + 1))),
      ∃ w0 e0 K : ℕ, DyadicMainCoprimeControl (MvPolynomial.rename s.symm F)
        (MvPolynomial.rename t.symm G) w0 e0 K) :
    ∃ w0 e0 K : ℕ, DyadicCoprimeControl F G w0 e0 K := by
  obtain ⟨w0, e0, K, hk⟩ := finite_uniform_dyadic_main_controls
    (fun st : Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin (n + 1)) =>
      MvPolynomial.rename st.1.symm F)
    (fun st : Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin (n + 1)) =>
      MvPolynomial.rename st.2.symm G)
    (fun st => h st.1 st.2)
  exact ⟨w0, e0, K, dyadicCoprimeControl_of_main_permutations F G (fun s t => hk (s, t))⟩

theorem exists_dyadic_common_prime_control {m n : ℕ}
    {F : MvPolynomial (Fin m) ℤ} {G : MvPolynomial (Fin n) ℤ}
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ w0 e0 K : ℕ, DyadicCoprimeControl F G w0 e0 K := by
  have H : ∀ k m n : ℕ, m + n = k →
      ∀ (F : MvPolynomial (Fin m) ℤ) (G : MvPolynomial (Fin n) ℤ),
        F ≠ 0 → G ≠ 0 → ∃ w0 e0 K : ℕ, DyadicCoprimeControl F G w0 e0 K := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m n hmn F G hF hG
      cases m with
      | zero =>
        exact ⟨(F.coeff 0).natAbs, 0, 0, dyadicCoprimeControl_empty_left F G⟩
      | succ m =>
        cases n with
        | zero =>
          exact ⟨(G.coeff 0).natAbs, 0, 0,
            dyadicCoprimeControl_swap (dyadicCoprimeControl_empty_left G F)⟩
        | succ n =>
          apply exists_dyadic_control_of_main_permutations F G
          intro s t
          let Fs := MvPolynomial.rename s.symm F
          let Gt := MvPolynomial.rename t.symm G
          have hFs : Fs ≠ 0 := integerPolynomial_permuted_ne_zero s hF
          have hGt : Gt ≠ 0 := integerPolynomial_permuted_ne_zero t hG
          apply exists_dyadic_main_control_of_lower_controls hFs hGt
          · exact ih (m + (n + 1)) (by omega) m (n + 1) rfl
              (integerPolynomialMainLeading Fs) Gt
              (integerPolynomialMainLeading_ne_zero hFs) hGt
          · exact ih ((m + 1) + n) (by omega) (m + 1) n rfl
              Fs (integerPolynomialMainLeading Gt)
              hFs (integerPolynomialMainLeading_ne_zero hGt)
  exact H (m + n) m n rfl F G hF hG

end Hindman168
