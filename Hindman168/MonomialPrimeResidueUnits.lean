import Hindman168.MonomialPrimeArithmetic
import Hindman168.RoughDenominatorUnits

/-!
# Monomial coefficients are units at every bounded positive modulus

Prime slots larger than the budget are coprime to every positive integer
within that budget. Their coefficient-one monomials remain units even at
composite moduli. The integer-evaluation residue is the actual coefficient.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem CoefficientOneMonomial.natAbs_eval_coprime_bounded {σ : Type*}
    {P : MvPolynomial σ ℤ} (hP : CoefficientOneMonomial P) (x : σ → ℕ)
    {V a : ℕ} (hx : ∀ i, (x i).Prime ∧ V < x i) (ha : 0 < a) (hcap : a ≤ V) :
    (MvPolynomial.eval (fun i => (x i : ℤ)) P).natAbs.Coprime a := by
  obtain ⟨e, rfl⟩ := hP
  rw [monomial_natAbs_eval]
  simp only [Finsupp.prod]
  exact Nat.Coprime.prod_left (fun i _ =>
    (large_prime_coprime_bounded (hx i).1 (hx i).2 ha hcap).pow_left (e i))

theorem CoefficientOneMonomial.eval₂_isUnit {σ T : Type*} [CommRing T]
    {P : MvPolynomial σ ℤ} (hP : CoefficientOneMonomial P) (φ : ℤ →+* T)
    (x : σ → T) (hx : ∀ i ∈ P.vars, IsUnit (x i)) :
    IsUnit (MvPolynomial.eval₂ φ x P) := by
  obtain ⟨e, rfl⟩ := hP
  simp only [MvPolynomial.eval₂_monomial, map_one, one_mul, Finsupp.prod]
  exact IsUnit.prod_iff.mpr (fun i hi => (hx i (by simpa using hi)).pow (e i))

theorem CoefficientOneMonomial.eval₂_isUnit_bounded {σ : Type*}
    {P : MvPolynomial σ ℤ} (hP : CoefficientOneMonomial P) (x : σ → ℕ)
    {V a : ℕ} (hx : ∀ i, (x i).Prime ∧ V < x i) (ha : 0 < a) (hcap : a ≤ V) :
    IsUnit (MvPolynomial.eval₂ (Int.castRingHom (ZMod a)) (fun i => (x i : ZMod a)) P) := by
  apply hP.eval₂_isUnit
  intro i _
  exact (ZMod.isUnit_iff_coprime (x i) a).mpr
    (large_prime_coprime_bounded (hx i).1 (hx i).2 ha hcap)

theorem integerPolynomialEval_residue {σ : Type*} (P : MvPolynomial σ ℤ)
    (x : σ → ℕ) (a : ℕ) :
    ((MvPolynomial.eval (fun i => (x i : ℤ)) P : ℤ) : ZMod a) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod a)) (fun i => (x i : ZMod a)) P := by
  simpa only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, RingHom.comp_id, Int.coe_castRingHom,
    Int.cast_natCast] using
    MvPolynomial.hom_eval₂ P (RingHom.id ℤ) (Int.castRingHom (ZMod a)) (fun i => (x i : ℤ))

theorem CoefficientOneMonomial.residue_isUnit_bounded {σ : Type*}
    {P : MvPolynomial σ ℤ} (hP : CoefficientOneMonomial P) (x : σ → ℕ)
    {V a : ℕ} (hx : ∀ i, (x i).Prime ∧ V < x i) (ha : 0 < a) (hcap : a ≤ V) :
    IsUnit ((MvPolynomial.eval (fun i => (x i : ℤ)) P : ℤ) : ZMod a) := by
  rw [integerPolynomialEval_residue]
  exact hP.eval₂_isUnit_bounded x hx ha hcap

end Hindman168
