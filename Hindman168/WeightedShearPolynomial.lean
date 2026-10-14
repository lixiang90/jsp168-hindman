import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Mathlib.Algebra.Module.Submodule.Lattice

/-!
The weighted polynomial filtration used in Lemma 7.7 of the Hindman paper.
The index is an integer so that the negative filtration levels really are zero.
The definitions concern actual multivariate polynomials, rather than an assumed
nilpotent action or an assumed degree-lowering operator.
-/

namespace Hindman168
open scoped BigOperators Pointwise
open MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- Polynomials whose monomials have weighted degree at most `d`. -/
def weightedShearDegreeLE (w : σ → ℕ) (d : ℤ) : Submodule R (MvPolynomial σ R) where
  carrier := {p | ∀ a ∈ p.support, (Finsupp.weight w a : ℤ) ≤ d}
  zero_mem' := by simp
  add_mem' := by
    classical
    intro p q hp hq a ha
    exact (Finset.mem_union.mp (MvPolynomial.support_add ha)).elim (hp a) (hq a)
  smul_mem' := by
    intro r p hp a ha
    exact hp a (MvPolynomial.support_smul ha)

@[simp] theorem mem_weightedShearDegreeLE (w : σ → ℕ) (d : ℤ)
    (p : MvPolynomial σ R) :
    p ∈ weightedShearDegreeLE w d ↔
      ∀ a ∈ p.support, (Finsupp.weight w a : ℤ) ≤ d := Iff.rfl

theorem weightedShearDegreeLE_mono (w : σ → ℕ) {d e : ℤ} (h : d ≤ e) :
    weightedShearDegreeLE (R := R) w d ≤ weightedShearDegreeLE w e :=
  fun _ hp a ha => (hp a ha).trans h

theorem weightedShearDegreeLE_neg (w : σ → ℕ) {d : ℤ} (hd : d < 0) :
    weightedShearDegreeLE (R := R) w d = ⊥ := by
  apply eq_bot_iff.mpr
  intro p hp
  change p = 0
  apply MvPolynomial.ext
  intro a
  simp only [coeff_zero]
  by_contra ha
  have h := hp a (MvPolynomial.mem_support_iff.mpr ha)
  have hn : (0 : ℤ) ≤ (Finsupp.weight w a : ℤ) := Int.natCast_nonneg _
  omega

theorem weightedShearDegreeLE_monomial (w : σ → ℕ) (a : σ →₀ ℕ) (r : R)
    {d : ℤ} (ha : (Finsupp.weight w a : ℤ) ≤ d) :
    monomial a r ∈ weightedShearDegreeLE w d := by
  classical
  intro b hb
  have hb' : b = a := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
  simpa only [hb'] using ha

theorem weightedShearDegreeLE_C (w : σ → ℕ) (r : R) :
    C r ∈ weightedShearDegreeLE w 0 := by
  exact weightedShearDegreeLE_monomial w 0 r (by simp)

theorem weightedShearDegreeLE_X (w : σ → ℕ) (i : σ) :
    (X i : MvPolynomial σ R) ∈ weightedShearDegreeLE w (w i) := by
  exact weightedShearDegreeLE_monomial w (Finsupp.single i 1) 1
    (by simp [Finsupp.weight_single])

theorem weightedShearDegreeLE_mul (w : σ → ℕ) {d e : ℤ}
    {p q : MvPolynomial σ R} (hp : p ∈ weightedShearDegreeLE w d)
    (hq : q ∈ weightedShearDegreeLE w e) :
    p * q ∈ weightedShearDegreeLE w (d + e) := by
  classical
  intro a ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q ha)
  simpa only [map_add, Nat.cast_add] using add_le_add (hp b hb) (hq c hc)

/-- A polynomial pair agrees up to a specified decrease of weighted degree. -/
def WeightedShearApprox (w : σ → ℕ) (k d : ℤ)
    (p q : MvPolynomial σ R) : Prop :=
  p ∈ weightedShearDegreeLE w d ∧ q ∈ weightedShearDegreeLE w d ∧
    p - q ∈ weightedShearDegreeLE w (d - k)

theorem WeightedShearApprox.mul {w : σ → ℕ} {k d e : ℤ}
    {p p' q q' : MvPolynomial σ R}
    (hp : WeightedShearApprox w k d p p') (hq : WeightedShearApprox w k e q q') :
    WeightedShearApprox w k (d + e) (p * q) (p' * q') := by
  refine ⟨weightedShearDegreeLE_mul w hp.1 hq.1,
    weightedShearDegreeLE_mul w hp.2.1 hq.2.1, ?_⟩
  have h₁ := weightedShearDegreeLE_mul w hp.2.2 hq.1
  have h₂ := weightedShearDegreeLE_mul w hp.2.1 hq.2.2
  have hsum : (p - p') * q + p' * (q - q') ∈ weightedShearDegreeLE w (d + e - k) := by
    apply Submodule.add_mem
    · simpa only [sub_add_eq_add_sub] using h₁
    · simpa only [← add_sub_assoc] using h₂
  convert hsum using 1
  ring

theorem WeightedShearApprox.refl_C (w : σ → ℕ) (k : ℤ) (r : R) :
    WeightedShearApprox w k 0 (C r) (C r) :=
  ⟨weightedShearDegreeLE_C w r, weightedShearDegreeLE_C w r,
    by simpa only [sub_self] using (weightedShearDegreeLE (R := R) w (0-k)).zero_mem⟩

theorem WeightedShearApprox.pow {w : σ → ℕ} {k d : ℤ}
    {p q : MvPolynomial σ R} (h : WeightedShearApprox w k d p q) (n : ℕ) :
    WeightedShearApprox w k ((n : ℤ) * d) (p ^ n) (q ^ n) := by
  induction n with
  | zero => simpa using WeightedShearApprox.refl_C w k (1 : R)
  | succ n ih =>
      simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul h

theorem WeightedShearApprox.prod {ι : Type*} {w : σ → ℕ} {k : ℤ}
    (A : Finset ι) (d : ι → ℤ) (p q : ι → MvPolynomial σ R)
    (h : ∀ i ∈ A, WeightedShearApprox w k (d i) (p i) (q i)) :
    WeightedShearApprox w k (∑ i ∈ A, d i) (∏ i ∈ A, p i) (∏ i ∈ A, q i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using WeightedShearApprox.refl_C w k (1 : R)
  | @insert i A hi ih =>
      simpa only [Finset.sum_insert hi, Finset.prod_insert hi] using
        (h i (Finset.mem_insert_self _ _)).mul
          (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- The exact coordinate condition for a degree-lowering polynomial substitution. -/
def WeightedShearSubstitution (w : σ → ℕ) (k : ℤ)
    (f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) : Prop :=
  ∀ i, f (X i) - X i ∈ weightedShearDegreeLE w ((w i : ℤ) - k)

/-- Every individual monomial is fixed modulo the lower weighted filtration. -/
theorem weightedShearSubstitution_monomial {w : σ → ℕ} {k : ℤ} (hk : 0 ≤ k)
    {f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R}
    (hf : WeightedShearSubstitution w k f) (a : σ →₀ ℕ) (r : R) :
    WeightedShearApprox w k (Finsupp.weight w a) (f (monomial a r)) (monomial a r) := by
  classical
  have hX : ∀ i, WeightedShearApprox w k (w i) (f (X i)) (X i) := by
    intro i
    have hx := weightedShearDegreeLE_X (R := R) w i
    refine ⟨?_, hx, hf i⟩
    have hdiff := weightedShearDegreeLE_mono w (show (w i : ℤ)-k ≤ w i by omega) (hf i)
    simpa only [sub_add_cancel] using (weightedShearDegreeLE w (w i)).add_mem hdiff hx
  have hprod := WeightedShearApprox.prod a.support (fun i => (a i : ℤ) * (w i : ℤ))
    (fun i => f (X i) ^ a i) (fun i => (X i : MvPolynomial σ R) ^ a i)
    (fun i _ => (hX i).pow (a i))
  have h := (WeightedShearApprox.refl_C w k r).mul hprod
  have hdeg : (∑ i ∈ a.support, (a i : ℤ) * (w i : ℤ)) =
      (Finsupp.weight w a : ℤ) := by
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
      Nat.cast_sum, Nat.cast_mul, Nat.cast_id]
  rw [zero_add, hdeg] at h
  simpa only [MvPolynomial.monomial_eq, map_mul, map_prod, map_pow,
    MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, Finsupp.prod] using h

/-- Actual strict coordinate shears lower the weighted degree of every polynomial.
This is the substitution-minus-identity assertion used in Lemma 7.7. -/
theorem weightedShearSubstitution_lowers {w : σ → ℕ} {k : ℤ} (hk : 0 ≤ k)
    {f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R}
    (hf : WeightedShearSubstitution w k f) {d : ℤ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedShearDegreeLE w d) :
    f p ∈ weightedShearDegreeLE w d ∧
      f p - p ∈ weightedShearDegreeLE w (d-k) := by
  classical
  have hmono := fun a => weightedShearSubstitution_monomial hk hf a (p.coeff a)
  have hid : f p = ∑ a ∈ p.support, f (monomial a (p.coeff a)) := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum]
  constructor
  · rw [hid]
    apply Submodule.sum_mem
    intro a ha
    exact weightedShearDegreeLE_mono w (hp a ha) (hmono a).1
  · have hdiff : f p - p = ∑ a ∈ p.support,
        (f (monomial a (p.coeff a)) - monomial a (p.coeff a)) := by
      rw [Finset.sum_sub_distrib, ← hid, ← p.as_sum]
    rw [hdiff]
    apply Submodule.sum_mem
    intro a ha
    exact weightedShearDegreeLE_mono w (sub_le_sub_right (hp a ha) k) (hmono a).2.2

/-- Every polynomial lies in a finite level of the actual weighted filtration. -/
theorem weightedShearDegreeLE_self (w : σ → ℕ) (p : MvPolynomial σ R) :
    p ∈ weightedShearDegreeLE w ((p.weightedTotalDegree w : ℕ) : ℤ) := by
  intro a ha
  exact_mod_cast MvPolynomial.le_weightedTotalDegree w ha

/-- A strict shear has no nonzero polynomial in its kernel. -/
theorem weightedShearSubstitution_eq_zero {w : σ → ℕ}
    {f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R}
    (hf : WeightedShearSubstitution w 1 f) (d : ℕ)
    {p : MvPolynomial σ R} (hp : p ∈ weightedShearDegreeLE w d) (hz : f p = 0) :
    p = 0 := by
  induction d with
  | zero =>
      have h := (weightedShearSubstitution_lowers (by norm_num) hf hp).2
      rw [hz, zero_sub, weightedShearDegreeLE_neg w (by norm_num)] at h
      simpa only [Submodule.mem_bot, neg_eq_zero] using h
  | succ d ih =>
      have h := (weightedShearSubstitution_lowers (by norm_num) hf hp).2
      rw [hz, zero_sub] at h
      have h' : -p ∈ weightedShearDegreeLE w d := by
        simpa only [Nat.cast_succ, add_sub_cancel_right] using h
      exact ih ((weightedShearDegreeLE w d).neg_mem_iff.mp h')

/-- Solving a strict polynomial shear preserves degree and produces a strict shear inverse.
The recursion is on polynomial degree, so no bijectivity premise is used. -/
theorem weightedShearSubstitution_preimage {w : σ → ℕ}
    {f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R}
    (hf : WeightedShearSubstitution w 1 f) (d : ℕ)
    {p : MvPolynomial σ R} (hp : p ∈ weightedShearDegreeLE w d) :
    ∃ q : MvPolynomial σ R, f q = p ∧ q ∈ weightedShearDegreeLE w d ∧
      q-p ∈ weightedShearDegreeLE w ((d : ℤ)-1) := by
  induction d generalizing p with
  | zero =>
      have h := (weightedShearSubstitution_lowers (by norm_num) hf hp).2
      rw [weightedShearDegreeLE_neg w (by norm_num), Submodule.mem_bot, sub_eq_zero] at h
      exact ⟨p, h, hp, by simp⟩
  | succ d ih =>
      have hd : f p-p ∈ weightedShearDegreeLE w d := by
        simpa only [Nat.cast_succ, add_sub_cancel_right] using
          (weightedShearSubstitution_lowers (by norm_num) hf hp).2
      obtain ⟨q, hq, hqdegree, _⟩ := ih hd
      refine ⟨p-q, ?_, ?_, ?_⟩
      · rw [map_sub, hq]
        abel
      · exact (weightedShearDegreeLE w (d+1)).sub_mem hp
          (weightedShearDegreeLE_mono w (by exact_mod_cast Nat.le_succ d) hqdegree)
      · have hneg := (weightedShearDegreeLE w d).neg_mem hqdegree
        have heq : p-q-p = -q := by abel
        rw [heq]
        simpa only [Nat.cast_succ, add_sub_cancel_right] using hneg

/-- Any polynomial substitution with strictly lower-weight displacement is bijective. -/
theorem weightedShearSubstitution_bijective {w : σ → ℕ}
    {f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R}
    (hf : WeightedShearSubstitution w 1 f) : Function.Bijective f := by
  constructor
  · intro p q hpq
    apply sub_eq_zero.mp
    apply weightedShearSubstitution_eq_zero hf ((p-q).weightedTotalDegree w)
      (weightedShearDegreeLE_self w (p-q))
    simp only [map_sub, hpq, sub_self]
  · intro p
    obtain ⟨q, hq, _, _⟩ := weightedShearSubstitution_preimage hf
      (p.weightedTotalDegree w) (weightedShearDegreeLE_self w p)
    exact ⟨q, hq⟩

/-- The genuine algebra automorphism associated with a strict polynomial shear. -/
noncomputable def weightedShearSubstitutionEquiv {w : σ → ℕ}
    (f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hf : WeightedShearSubstitution w 1 f) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofBijective f (weightedShearSubstitution_bijective hf)

/-- A shear's inverse is again a strict shear, proved from the coordinate condition alone. -/
theorem weightedShearSubstitution_inv {w : σ → ℕ}
    {f : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R}
    (hf : WeightedShearSubstitution w 1 f.toAlgHom) :
    WeightedShearSubstitution w 1 f.symm.toAlgHom := by
  intro i
  obtain ⟨q, hq, _, hdiff⟩ := weightedShearSubstitution_preimage hf
    (w i) (weightedShearDegreeLE_X (R := R) w i)
  have heq : q = f.symm (X i) := by
    apply f.injective
    change f q = X i at hq
    simpa only [AlgEquiv.apply_symm_apply] using hq
  change f.symm (X i)-X i ∈ weightedShearDegreeLE w ((w i : ℤ)-1)
  simpa only [heq] using hdiff

/-- The defining displacement polynomials directly give the degree-lowering substitution. -/
theorem weightedShearSubstitution_aeval (w : σ → ℕ) (p : σ → MvPolynomial σ R)
    (hp : ∀ i, p i ∈ weightedShearDegreeLE w ((w i : ℤ)-1)) :
    WeightedShearSubstitution w 1 (MvPolynomial.aeval (fun i => X i + p i)) := by
  intro i
  simpa only [MvPolynomial.aeval_X, add_sub_cancel_left] using hp i

end Hindman168
