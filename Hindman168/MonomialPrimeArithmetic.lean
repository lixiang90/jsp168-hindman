import Hindman168.MaskGeneratedMonomialCertificates
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Actual monomial evaluations: units and coprime column coefficients

No repeated prime is allowed in the local tuple. Within one certified row,
variable-disjoint columns then evaluate to coprime natural absolute values.
Nonzero coefficients are products of pool primes with exact multiplicity.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem monomial_natAbs_eval {σ : Type*} (e : σ →₀ ℕ) (x : σ → ℕ) :
    (MvPolynomial.eval (fun i => (x i : ℤ)) (MvPolynomial.monomial e 1)).natAbs =
      e.prod (fun i v => x i ^ v) := by
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod,
    ← Nat.cast_pow, ← Nat.cast_prod, Int.natAbs_natCast]

theorem CoefficientOneMonomial.eval₂_ne_zero {σ T : Type*}
    [CommRing T] [IsDomain T] {P : MvPolynomial σ ℤ} (hP : CoefficientOneMonomial P)
    (φ : ℤ →+* T) (x : σ → T) (hx : ∀ i ∈ P.vars, x i ≠ 0) :
    MvPolynomial.eval₂ φ x P ≠ 0 := by
  obtain ⟨e, rfl⟩ := hP
  simp only [MvPolynomial.eval₂_monomial, map_one, one_mul, Finsupp.prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply pow_ne_zero
  exact hx i (by simpa using hi)

theorem CoefficientOneMonomial.natAbs_eval_pos {σ : Type*} {P : MvPolynomial σ ℤ}
    (hP : CoefficientOneMonomial P) (x : σ → ℕ) (hx : ∀ i, 0 < x i) :
    0 < (MvPolynomial.eval (fun i => (x i : ℤ)) P).natAbs := by
  obtain ⟨e, rfl⟩ := hP
  rw [monomial_natAbs_eval]
  exact Finset.prod_pos (fun i _ => pow_pos (hx i) _)

theorem CoefficientOneMonomial.coprime_evaluations {σ : Type*}
    {P Q : MvPolynomial σ ℤ} (hP : CoefficientOneMonomial P) (hQ : CoefficientOneMonomial Q)
    (hdis : Disjoint P.vars Q.vars) (x : σ → ℕ) (hx : ∀ i, (x i).Prime)
    (hinj : Function.Injective x) :
    (MvPolynomial.eval (fun i => (x i : ℤ)) P).natAbs.Coprime
      (MvPolynomial.eval (fun i => (x i : ℤ)) Q).natAbs := by
  obtain ⟨e, rfl⟩ := hP
  obtain ⟨f, rfl⟩ := hQ
  have hd : Disjoint e.support f.support := by simpa using hdis
  rw [monomial_natAbs_eval, monomial_natAbs_eval]
  simp only [Finsupp.prod]
  apply Nat.Coprime.prod_left
  intro i hi
  apply Nat.Coprime.prod_right
  intro j hj
  apply Nat.coprime_pow_primes _ _ (hx i) (hx j)
  intro hij
  have heq : i = j := hinj hij
  subst j
  exact Finset.disjoint_left.mp hd hi hj

theorem PolynomialMonomialRow.disjoint_column_vars {n c : ℕ}
    {A : Fin c → MvPolynomial (Fin n) ℤ} (hA : PolynomialMonomialRow A)
    (j k : Fin c) (hne : j ≠ k) : Disjoint (A j).vars (A k).vars := by
  apply Finset.disjoint_left.mpr
  intro v hvj hvk
  exact hne (hA.variable_unique v j k hvj hvk)

theorem PolynomialMonomialRow.coprime_nonzero_columns {n c : ℕ}
    {A : Fin c → MvPolynomial (Fin n) ℤ} (hA : PolynomialMonomialRow A)
    (j k : Fin c) (hne : j ≠ k) (hj : A j ≠ 0) (hk : A k ≠ 0)
    (x : Fin n → ℕ) (hx : ∀ i, (x i).Prime) (hinj : Function.Injective x) :
    (MvPolynomial.eval (fun i => (x i : ℤ)) (A j)).natAbs.Coprime
      (MvPolynomial.eval (fun i => (x i : ℤ)) (A k)).natAbs :=
  (hA.monomial_of_ne_zero j hj).coprime_evaluations (hA.monomial_of_ne_zero k hk)
    (hA.disjoint_column_vars j k hne) x hx hinj

end Hindman168
