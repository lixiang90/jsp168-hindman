import Hindman168.NilpotentPolynomialDexp

/-! A polynomial with zero constant term and nilpotent values in the
polynomial algebra lies coefficientwise in V if its actual right logarithmic
exponential derivative does. The proof uses the proved dexp formula and
induction on coefficient degree; BCH coefficient membership is not assumed. -/

noncomputable section
namespace Hindman168
open Polynomial Module Finset

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Algebra ℚ R] [Algebra ℚ A]
local instance recursionAmbientLieRing : LieRing A := LieRing.ofAssociativeRing
local instance recursionPolynomialLieRing : LieRing (Polynomial A) := LieRing.ofAssociativeRing

 omit [Algebra ℚ R] in
 theorem polynomial_commutator_coeff_mem_constant_zero
    (V : LieSubalgebra R A) {p q : Polynomial A} (h0 : p.coeff 0 = 0) (n : ℕ)
    (hp : ∀ i ≤ n, p.coeff i ∈ V) (hq : ∀ j < n, q.coeff j ∈ V) :
    (commutatorEndQ p q).coeff n ∈ V := by
  rw [commutatorEndQ_apply, polynomial_commutator_coeff]
  apply V.toSubmodule.sum_mem
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1 = 0
  · rw [hi, h0, zero_mul, mul_zero, sub_self]
    exact V.zero_mem
  · exact V.lie_mem (hp ij.1 (by omega)) (hq ij.2 (by omega))

 omit [Algebra ℚ R] in
 theorem polynomial_ad_pow_coeff_mem_constant_zero
    (V : LieSubalgebra R A) {p q : Polynomial A} (h0 : p.coeff 0 = 0) (n m : ℕ)
    (hp : ∀ i ≤ n, p.coeff i ∈ V) (hq : ∀ j < n, q.coeff j ∈ V) :
    ((commutatorEndQ p ^ (m + 1)) q).coeff n ∈ V := by
  induction m generalizing n with
  | zero =>
    simpa only [Nat.zero_add, pow_one] using
      polynomial_commutator_coeff_mem_constant_zero V h0 n hp hq
  | succ m ih =>
    rw [pow_succ']
    change (commutatorEndQ p ((commutatorEndQ p ^ (m + 1)) q)).coeff n ∈ V
    apply polynomial_commutator_coeff_mem_constant_zero V h0 n hp
    intro j hj
    exact ih j (fun i hi => hp i (by omega)) (fun i hi => hq i (by omega))

 theorem polynomialLieSubalgebra_of_right_log_derivative
    (V : LieSubalgebra R A) {p : Polynomial A}
    (h0 : p.coeff 0 = 0) (hn : IsNilpotent p)
    (hd : (IsNilpotent.exp p).derivative * IsNilpotent.exp (-p) ∈ polynomialLieSubalgebra V) :
    p ∈ polynomialLieSubalgebra V := by
  obtain ⟨m, hm, he⟩ := polynomial_nilpotent_exp_dexp hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm)
  rw [Finset.sum_range_succ'] at he
  simp only [Nat.zero_add, Nat.factorial_one, Nat.cast_one, inv_one, pow_zero,
    Module.End.one_apply, one_smul] at he
  have hbound : ∀ n, ∀ i ≤ n, p.coeff i ∈ V := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have hi0 : i = 0 := by omega
      rw [hi0, h0]
      exact V.zero_mem
    | succ n ih =>
      have hdp : ∀ j < n, p.derivative.coeff j ∈ V := by
        intro j hj
        rw [coeff_derivative, ← Nat.cast_add_one, ← nsmul_eq_mul']
        exact V.toSubmodule.nsmul_mem (ih (j + 1) (by omega)) (j + 1)
      have hs : (∑ k ∈ range m, ((k + 1 + 1).factorial : ℚ)⁻¹ •
          ((commutatorEndQ p ^ (k + 1)) p.derivative)).coeff n ∈ V := by
        rw [finsetSum_coeff]
        apply V.toSubmodule.sum_mem
        intro k _
        rw [coeff_smul]
        exact (V.toSubmodule.restrictScalars ℚ).smul_mem _
          (polynomial_ad_pow_coeff_mem_constant_zero V h0 n k ih hdp)
      have hcoef := congrArg (fun q : Polynomial A => q.coeff n) he
      rw [coeff_add] at hcoef
      have hder : p.derivative.coeff n ∈ V := by
        have hv := V.sub_mem (hd n) hs
        rw [hcoef, add_sub_cancel_left] at hv
        exact hv
      have hnext : p.coeff (n + 1) ∈ V := by
        rw [polynomial_coeff_from_derivative]
        exact (V.toSubmodule.restrictScalars ℚ).smul_mem _ hder
      intro i hi
      by_cases hin : i ≤ n
      · exact ih i hin
      · have hieq : i = n + 1 := by omega
        rw [hieq]
        exact hnext
  intro n
  exact hbound n n le_rfl

end Hindman168
