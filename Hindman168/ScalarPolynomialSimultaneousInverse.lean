import Hindman168.ScalarPolynomialTopStripping
import Hindman168.ScalarPolynomialRecoveryModOne
import Hindman168.ModOneNaturalMultiplier

namespace Hindman168
open Polynomial
open scoped Classical

/-- Genuine simultaneous scalar Weyl inverse: one bounded positive
multiplier controls every original nonconstant monomial coefficient. All
constants precede the polynomial and N. Actual top stripping and integer
coefficient recovery discharge the complete natural degree induction. -/
theorem scalar_polynomial_phase_simultaneous_inverse (D : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ p : ℝ[X], p.natDegree ≤ D → ∀ N : ℕ, 0 < N →
      δ ≤ ‖finiteComplexSetMean (Finset.range N) (scalarPolynomialPhase p)‖ →
      ∃ Q : ℕ, 0 < Q ∧ Q ≤ A ∧ ∀ i : ℕ, 0 < i → i ≤ D →
        (N : ℝ)^i*‖(((Q : ℝ)*p.coeff i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  induction D generalizing δ with
  | zero =>
    refine ⟨1, by omega, ?_⟩
    intro p hp N hN hmean
    refine ⟨1, by omega, le_rfl, ?_⟩
    intro i hi hiD
    omega
  | succ D ih =>
    obtain ⟨B, M, ρ, hB, hM, hρ, hρ1, hstrip⟩ := scalar_polynomial_top_stripping D δ hδ hδ1
    obtain ⟨K, hK, hlowInv⟩ := ih (δ/4) (by positivity) (by linarith)
    let C := (D+1 : ℕ)*(B : ℝ)^(D+1)*(2 : ℝ)^D*(K : ℝ)/(ρ/2)^D
    let A := K*B^(D+1)+⌈C⌉₊+M^(D+1)+1
    have hA : 0 < A := by dsimp only [A]; omega
    have hKA : K*B^(D+1) ≤ A := by dsimp only [A]; omega
    have hMA : M^(D+1) ≤ A := by dsimp only [A]; omega
    have hCA : C ≤ A := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈C⌉₊ ≤ A by dsimp only [A]; omega))
    refine ⟨A, hA, ?_⟩
    intro p hp N hN hmean
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    by_cases hMN : M ≤ N
    · obtain ⟨q, a, H, hq, hqB, ha, hHdef, hH, hHlow, hHup, hindices, htop, hdeg, hlow⟩ :=
        hstrip p hp N hMN hmean
      obtain ⟨k, hk, hkK, hcoeff⟩ := hlowInv
        (scalarPolynomialOnProgression (scalarPolynomialDropTop p (D+1)) a q) hdeg H hH hlow
      let Q := k*q^(D+1)
      have hQ : 0 < Q := by dsimp only [Q]; positivity
      have hQK : Q ≤ K*B^(D+1) :=
        Nat.mul_le_mul hkK (Nat.pow_le_pow_left hqB (D+1))
      have hqBr : (q : ℝ) ≤ B := by exact_mod_cast hqB
      have hkKr : (k : ℝ) ≤ K := by exact_mod_cast hkK
      have hqpow : (q : ℝ)^D ≤ (B : ℝ)^D := pow_le_pow_left₀ (Nat.cast_nonneg q) hqBr D
      refine ⟨Q, hQ, hQK.trans hKA, ?_⟩
      intro i hi hiD
      by_cases hiTop : i=D+1
      · subst i
        have he : (Q : ℝ)*p.coeff (D+1) =
            ((k*q^D : ℕ) : ℝ)*((q : ℝ)*p.coeff (D+1)) := by
          dsimp only [Q]
          push_cast
          rw [pow_succ]
          ring
        rw [he]
        have hmul := mod_one_natural_multiplier_norm_le (k*q^D) ((q : ℝ)*p.coeff (D+1))
        have hsize : ((k*q^D : ℕ) : ℝ) ≤ (K : ℝ)*(B : ℝ)^D := by
          push_cast
          exact mul_le_mul hkKr hqpow (by positivity) (by positivity)
        calc
          _ ≤ (N : ℝ)^(D+1)*(((k*q^D : ℕ) : ℝ)*
              ‖(((q : ℝ)*p.coeff (D+1) : ℝ) : UnitAddCircle)‖) :=
            mul_le_mul_of_nonneg_left hmul (pow_nonneg hNr.le _)
          _ = ((k*q^D : ℕ) : ℝ)*((N : ℝ)^(D+1)*
              ‖(((q : ℝ)*p.coeff (D+1) : ℝ) : UnitAddCircle)‖) := by ring
          _ ≤ ((k*q^D : ℕ) : ℝ)*(B : ℝ) := mul_le_mul_of_nonneg_left htop (by positivity)
          _ ≤ ((K : ℝ)*(B : ℝ)^D)*(B : ℝ) := mul_le_mul_of_nonneg_right hsize (by positivity)
          _ = (K*B^(D+1) : ℕ) := by push_cast; rw [pow_succ]; ring
          _ ≤ A := by exact_mod_cast hKA
      · have hiLow : i ≤ D := by omega
        have hdrop : (scalarPolynomialDropTop p (D+1)).coeff i = p.coeff i := by
          rw [scalarPolynomialDropTop, coeff_sub, coeff_monomial, if_neg (by omega), sub_zero]
        have hHL : (ρ/2)*(N : ℝ) ≤ (H : ℝ) := by nlinarith only [hHlow]
        have hrec := scalar_polynomial_recovery_mod_one (scalarPolynomialDropTop p (D+1))
          a q D i N H k (scalar_polynomial_drop_top_degree p D hp) hq ha.le hN hi
          (ρ/2) (K : ℝ) (by positivity) (by linarith) (Nat.cast_nonneg K) hHL hcoeff
        rw [hdrop] at hrec
        have he : (Q : ℝ)*p.coeff i =
            (q : ℝ)*(((k*q^D : ℕ) : ℝ)*p.coeff i) := by
          dsimp only [Q]
          push_cast
          rw [pow_succ]
          ring
        rw [he]
        have hmul := mod_one_natural_multiplier_norm_le q (((k*q^D : ℕ) : ℝ)*p.coeff i)
        have hNq : (N : ℝ)^i*‖(((q : ℝ)*(((k*q^D : ℕ) : ℝ)*p.coeff i) : ℝ) : UnitAddCircle)‖ ≤
            (q : ℝ)*((D+1 : ℕ)*(q : ℝ)^D*(2 : ℝ)^D*(K : ℝ)/(ρ/2)^D) := by
          calc
            _ ≤ (N : ℝ)^i*((q : ℝ)*‖((((k*q^D : ℕ) : ℝ)*p.coeff i : ℝ) : UnitAddCircle)‖) :=
              mul_le_mul_of_nonneg_left hmul (pow_nonneg hNr.le _)
            _ = (q : ℝ)*((N : ℝ)^i*‖((((k*q^D : ℕ) : ℝ)*p.coeff i : ℝ) : UnitAddCircle)‖) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg q)
        let F := (D+1 : ℕ)*(2 : ℝ)^D*(K : ℝ)/(ρ/2)^D
        have hbudget : (q : ℝ)*((D+1 : ℕ)*(q : ℝ)^D*(2 : ℝ)^D*(K : ℝ)/(ρ/2)^D) ≤ C := by
          calc
            _ = F*(q : ℝ)^(D+1) := by dsimp only [F]; rw [pow_succ]; ring
            _ ≤ F*(B : ℝ)^(D+1) := mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (Nat.cast_nonneg q) hqBr _) (by dsimp only [F]; positivity)
            _ = C := by dsimp only [C, F]; ring
        exact hNq.trans (hbudget.trans hCA)
    · have hNM : (N : ℝ) ≤ M := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hMN))
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
      refine ⟨1, by omega, hA, ?_⟩
      intro i hi hiD
      have hpw : (N : ℝ)^i ≤ (M : ℝ)^(D+1) :=
        (pow_le_pow_left₀ hNr.le hNM i).trans (pow_le_pow_right₀ hM1 hiD)
      have hnorm : ‖((p.coeff i : ℝ) : UnitAddCircle)‖ ≤ 1 := by
        have hh := AddCircle.norm_le_half_period (1 : ℝ) (x := ((p.coeff i : ℝ) : UnitAddCircle))
          (by norm_num)
        norm_num at hh
        linarith
      simp only [Nat.cast_one, one_mul]
      have hb : (N : ℝ)^i*‖((p.coeff i : ℝ) : UnitAddCircle)‖ ≤ (N : ℝ)^i := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hnorm (pow_nonneg hNr.le i)
      exact hb.trans (hpw.trans (by exact_mod_cast hMA))

end Hindman168
