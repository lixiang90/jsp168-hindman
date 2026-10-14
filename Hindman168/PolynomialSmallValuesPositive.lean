import Hindman168.PolynomialSmallValuesPositiveNonconstant
import Hindman168.PolynomialSmallValueConstantRecovery

namespace Hindman168
open Polynomial
open scoped Classical

/-- Actual positive-tolerance small-value inverse, INCLUDING the constant
and with a fixed large-N threshold. One actual multiplier controls all
original coefficients with the same epsilon-dependent budget. -/
theorem polynomial_small_values_positive (D : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ A T : ℕ, 0 < A ∧ 0 < T ∧ ∀ p : ℝ[X], p.natDegree ≤ D →
      ∀ N : ℕ, T ≤ N → ∀ ε : ℝ, 0 < ε → ε ≤ δ/10 →
        δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
          ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε)).card →
        ∃ q : ℕ, 0 < q ∧ q ≤ A ∧ ∀ i : ℕ, i ≤ D →
          (N : ℝ)^i*‖(((q : ℝ)*p.coeff i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)*ε := by
  obtain ⟨S, T, C, hS, hT, hC, hinv⟩ := polynomial_small_values_positive_nonconstant D δ hδ hδ1
  let A := S+⌈C⌉₊+⌈(S : ℝ)+(D : ℝ)*C⌉₊+1
  have hA : 0 < A := by dsimp only [A]; omega
  have hSA : S ≤ A := by dsimp only [A]; omega
  have hCA : C ≤ A := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈C⌉₊ ≤ A by dsimp only [A]; omega))
  have hConstA : (S : ℝ)+(D : ℝ)*C ≤ A := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈(S : ℝ)+(D : ℝ)*C⌉₊ ≤ A by dsimp only [A]; omega))
  refine ⟨A, T, hA, hT, ?_⟩
  intro p hp N hTN ε hε hεsmall hdense
  obtain ⟨q, hq, hqS, hcoeff⟩ := hinv p hp N hTN ε hε hεsmall hdense
  have hN : 0 < N := hT.trans_le hTN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsnon : ((Finset.range N).filter (fun n : ℕ =>
      ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε)).Nonempty := by
    apply Finset.card_pos.mp
    have hh := lt_of_lt_of_le (mul_pos hδ hNr) hdense
    exact_mod_cast hh
  obtain ⟨n, hn⟩ := hsnon
  have hnv := Finset.mem_filter.mp hn
  have hconst := polynomial_small_value_constant_recovery p D n N q hp
    (Finset.mem_range.mp hnv.1).le ε C hnv.2 hcoeff
  have hqSr : (q : ℝ) ≤ S := by exact_mod_cast hqS
  have hconstA : ‖(((q : ℝ)*p.coeff 0 : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)*ε := by
    have hh := mul_le_mul_of_nonneg_right hqSr hε.le
    have hb := mul_le_mul_of_nonneg_right hConstA hε.le
    nlinarith
  refine ⟨q, hq, hqS.trans hSA, ?_⟩
  intro i hiD
  by_cases hi : i=0
  · subst i
    simpa only [pow_zero, one_mul] using hconstA
  · exact (hcoeff i (Nat.pos_of_ne_zero hi) hiD).trans
      (mul_le_mul_of_nonneg_right hCA hε.le)

end Hindman168
