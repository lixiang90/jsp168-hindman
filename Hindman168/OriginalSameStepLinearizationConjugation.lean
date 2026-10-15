import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Algebra.Lie.OfAssociative
import OAI.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder

/-! Algebraic adjoint-exponential identities used by same-step linearization. -/

namespace Hindman168
namespace OriginalSameStepLinearizationConjugation

open IsNilpotent
open OAI.Erdos3

section Lie

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

/-- The finite Hadamard sum.  For an `s`-step algebra, all terms from `s` onward vanish. -/
noncomputable def adjointSum (s : ℕ) (a b : L) : L :=
  ∑ n ∈ Finset.range s, ((n.factorial : ℚ)⁻¹) • (LieAlgebra.ad ℚ L a ^ n) b

theorem map_ad_pow (φ : L →ₗ⁅ℚ⁆ M) (a b : L) (n : ℕ) :
    φ ((LieAlgebra.ad ℚ L a ^ n) b) = (LieAlgebra.ad ℚ M (φ a) ^ n) (φ b) := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', Module.End.mul_apply, LieHom.map_lie, ih]

theorem map_adjointSum (φ : L →ₗ⁅ℚ⁆ M) (s : ℕ) (a b : L) :
    φ (adjointSum s a b) = adjointSum s (φ a) (φ b) := by
  simp [adjointSum, map_ad_pow]

@[simp] theorem adjointSum_zero (s : ℕ) (a : L) : adjointSum s a 0 = 0 := by
  simp [adjointSum]

theorem adjointSum_add (s : ℕ) (a b c : L) :
    adjointSum s a (b + c) = adjointSum s a b + adjointSum s a c := by
  simp [adjointSum, map_add, smul_add, Finset.sum_add_distrib]

end Lie

section Associative

variable {A : Type*} [Ring A] [Algebra ℚ A]
attribute [local instance] LieRing.ofAssociativeRing

private theorem nilpotent_mulLeft {a : A} (ha : IsNilpotent a) :
    IsNilpotent (LinearMap.mulLeft ℚ a) := by
  obtain ⟨n, hn⟩ := ha
  refine ⟨n, ?_⟩
  ext b
  simp [hn]

private theorem nilpotent_mulRight {a : A} (ha : IsNilpotent a) :
    IsNilpotent (LinearMap.mulRight ℚ a) := by
  obtain ⟨n, hn⟩ := ha
  refine ⟨n, ?_⟩
  ext b
  simp [hn]

private theorem exp_mulLeft_apply {a : A} (ha : IsNilpotent a) (b : A) :
    exp (LinearMap.mulLeft ℚ a) b = exp a * b := by
  obtain ⟨n, hn⟩ := ha
  have hL : LinearMap.mulLeft ℚ a ^ n = 0 := by
    ext c
    simp [hn]
  simp [exp_eq_sum hL, exp_eq_sum hn, Finset.sum_mul]

private theorem exp_mulRight_apply {a : A} (ha : IsNilpotent a) (b : A) :
    exp (LinearMap.mulRight ℚ a) b = b * exp a := by
  obtain ⟨n, hn⟩ := ha
  have hR : LinearMap.mulRight ℚ a ^ n = 0 := by
    ext c
    simp [hn]
  simp [exp_eq_sum hR, exp_eq_sum hn, Finset.mul_sum]

/-- Hadamard's identity in a rational associative algebra, with algebraic exponentials. -/
theorem exp_ad_eq_conjugation {a : A} (ha : IsNilpotent a) (b : A) :
    exp (LieAlgebra.ad ℚ A a) b = exp a * b * exp (-a) := by
  have had : LieAlgebra.ad ℚ A a =
      LinearMap.mulLeft ℚ a + LinearMap.mulRight ℚ (-a) := by
    ext c
    simp [LieRing.of_associative_ring_bracket, sub_eq_add_neg]
  have hc : Commute (LinearMap.mulLeft ℚ a) (LinearMap.mulRight ℚ (-a)) := by
    ext c
    simp [mul_assoc]
  rw [had, exp_add_of_commute hc (nilpotent_mulLeft ha) (nilpotent_mulRight ha.neg),
    Module.End.mul_apply, exp_mulLeft_apply ha, exp_mulRight_apply ha.neg]
  exact (mul_assoc _ _ _).symm

/-- Nilpotent associative elements induce nilpotent adjoint operators. -/
theorem nilpotent_ad {a : A} (ha : IsNilpotent a) :
    IsNilpotent (LieAlgebra.ad ℚ A a) := by
  have had : LieAlgebra.ad ℚ A a =
      LinearMap.mulLeft ℚ a + LinearMap.mulRight ℚ (-a) := by
    ext c
    simp [LieRing.of_associative_ring_bracket, sub_eq_add_neg]
  rw [had]
  have hc : Commute (LinearMap.mulLeft ℚ a) (LinearMap.mulRight ℚ (-a)) := by
    ext c
    simp [mul_assoc]
  exact hc.isNilpotent_add (nilpotent_mulLeft ha) (nilpotent_mulRight ha.neg)

/-- Conjugation by the exponential as a genuine ring homomorphism. -/
noncomputable def expConjugationHom (a : A) (ha : IsNilpotent a) : A →+* A where
  toFun b := exp a * b * exp (-a)
  map_one' := by simpa using exp_mul_exp_neg_self ha
  map_mul' b c := by
    have hi := exp_neg_mul_exp_self ha
    calc
      exp a * (b * c) * exp (-a) = exp a * b * 1 * c * exp (-a) := by
        simp [mul_assoc]
      _ = (exp a * b * exp (-a)) * (exp a * c * exp (-a)) := by
        rw [← hi]
        simp only [mul_assoc]
  map_zero' := by simp
  map_add' b c := by simp [mul_add, add_mul]

/-- The associative BCH conjugation identity, before introducing the finite sum. -/
theorem nilpotentBCH_conjugation (I : NonUnitalSubalgebra ℚ A)
    (hI : ∀ a ∈ I, IsNilpotent a) {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    nilpotentBCH (nilpotentBCH a b) (-a) = exp (LieAlgebra.ad ℚ A a) b := by
  have hna := hI _ ha
  have hnb := hI _ hb
  have hab := nilpotentBCH_mem I ha hb hna hnb
  have hnab := hI _ hab
  have hneg := I.neg_mem ha
  rw [exp_ad_eq_conjugation hna]
  apply exp_injective_on_nilpotents
    (hI _ (nilpotentBCH_mem I hab hneg hnab hna.neg))
    (hnb.map (expConjugationHom a hna))
  rw [exp_nilpotentBCH I hI hab hneg, exp_nilpotentBCH I hI ha hb]
  exact IsNilpotent.map_exp hnb (expConjugationHom a hna)

variable {s : ℕ} (F : NilpotentAlgebraFiltration A s)

/-- Each adjoint raises the associative filtration by one. -/
theorem ad_pow_mem_layer {a b : A} (ha : a ∈ F.layer 1)
    {i : ℕ} (hb : b ∈ F.layer i) (n : ℕ) :
    (LieAlgebra.ad ℚ A a ^ n) b ∈ F.layer (n + i) := by
  induction n with
  | zero => simpa using hb
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    simpa only [LieAlgebra.ad_apply, LieRing.of_associative_ring_bracket,
      Nat.succ_add, Nat.one_add, Nat.add_assoc, Nat.zero_add] using F.ring_commutator_mem ha ih

/-- The full adjoint operator is nilpotent with the explicit filtration bound. -/
theorem ad_pow_succ_eq_zero {a : A} (ha : a ∈ F.layer 1) :
    LieAlgebra.ad ℚ A a ^ (s + 1) = 0 := by
  ext b
  have hb : b ∈ F.layer 0 := by simp [F.zero_eq_top]
  have h := ad_pow_mem_layer F ha hb (s + 1)
  simpa only [Nat.add_zero, F.terminal, Submodule.mem_bot, LinearMap.zero_apply] using h

/-- On a positive-filtration input, the last term also vanishes. -/
theorem ad_pow_step_apply_eq_zero {a b : A}
    (ha : a ∈ F.layer 1) (hb : b ∈ F.layer 1) :
    (LieAlgebra.ad ℚ A a ^ s) b = 0 := by
  have h := ad_pow_mem_layer F ha hb s
  simpa only [F.terminal, Submodule.mem_bot] using h

/-- Algebraic adjoint exponentiation is exactly the finite Hadamard sum. -/
theorem exp_ad_eq_adjointSum {a b : A}
    (ha : a ∈ F.layer 1) (hb : b ∈ F.layer 1) :
    exp (LieAlgebra.ad ℚ A a) b = adjointSum s a b := by
  rw [exp_eq_sum (ad_pow_succ_eq_zero F ha)]
  simp [adjointSum, Finset.sum_range_succ, ad_pow_step_apply_eq_zero F ha hb]

/-- Finite Hadamard identity in a nilpotently filtered associative algebra. -/
theorem filtered_BCH_conjugation {a b : A}
    (ha : a ∈ F.layer 1) (hb : b ∈ F.layer 1) :
    nilpotentBCH (nilpotentBCH a b) (-a) = adjointSum s a b := by
  rw [nilpotentBCH_conjugation (F.layerAlgebra 1) F.positive_nilpotent ha hb,
    exp_ad_eq_adjointSum F ha hb]

end Associative

section GeneralLie

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
attribute [local instance] LieRing.ofAssociativeRing

/-- Finite Hadamard conjugation, for every rational nilpotent Lie algebra.
The nilpotence hypothesis is precisely the original step `s`. -/
theorem lieBCH_conjugation_eq_adjointSum
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (a b : L) :
    lieBCH s (lieBCH s a b) (-a) = adjointSum s a b := by
  let x : Fin 2 → FreeLieAlgebra ℚ (Fin 2) := FreeLieAlgebra.of ℚ
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 2)) s
  have hx (i : Fin 2) : scaledFreeGenerator s i ∈ F.layer 1 :=
    scaledFreeGenerator_mem_layer s i
  have h : scaledFreeLieEval s (lieBCH s (lieBCH s (x 0) (x 1)) (-x 0)) =
      scaledFreeLieEval s (adjointSum s (x 0) (x 1)) := by
    simp only [map_lieBCH, map_neg, map_adjointSum, x, scaledFreeLieEval_of]
    rw [F.lieBCH_eq (hx 0) (hx 1),
      F.lieBCH_eq (F.bch_mem le_rfl (hx 0) (hx 1)) ((F.layer 1).neg_mem (hx 0))]
    exact filtered_BCH_conjugation F (hx 0) (hx 1)
  have he := lie_lift_eq_of_scaledFreeLieEval_eq ![a, b] hnil h
  simpa only [map_lieBCH, map_neg, map_adjointSum, x,
    FreeLieAlgebra.lift_of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using he

/-- Group-coordinate form of the finite Hadamard identity. -/
theorem conjugation_coord (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (a b : NilpotentLieBCHGroup L s hnil) :
    (a * b * a⁻¹).coord = adjointSum s a.coord b.coord := by
  exact lieBCH_conjugation_eq_adjointSum hnil a.coord b.coord

end GeneralLie

section ScalarExtension

open scoped TensorProduct

variable {R L M : Type*} [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

/-- The adjoint iterates of a rational direction commute with scalar extension. -/
theorem ad_pow_tmul (a b : L) (r : R) (n : ℕ) :
    (LieAlgebra.ad ℚ (R ⊗[ℚ] L) (1 ⊗ₜ[ℚ] a) ^ n) (r ⊗ₜ[ℚ] b) =
      r ⊗ₜ[ℚ] (LieAlgebra.ad ℚ L a ^ n) b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, ih]

/-- Finite Hadamard is compatible with pure tensors, with arbitrary scalar coefficients. -/
theorem adjointSum_tmul (s : ℕ) (a b : L) (r : R) :
    adjointSum s (1 ⊗ₜ[ℚ] a) (r ⊗ₜ[ℚ] b) = r ⊗ₜ[ℚ] adjointSum s a b := by
  simp [adjointSum, ad_pow_tmul, TensorProduct.tmul_sum, TensorProduct.tmul_smul]

/-- A rational finite-adjoint identity extends to all scalar-extended inputs.
Only the time direction stays rational; the input tensor is arbitrary. -/
theorem adjointSum_baseChange (s : ℕ) (a : M) (i : L →ₗ[ℚ] M) (T : L →ₗ[ℚ] L)
    (h : ∀ b, adjointSum s a (i b) = i (T b)) (b : R ⊗[ℚ] L) :
    adjointSum s (1 ⊗ₜ[ℚ] a) (i.baseChange R b) =
      i.baseChange R (T.baseChange R b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul r b => simp only [LinearMap.baseChange_tmul, adjointSum_tmul, h]
  | add x y hx hy => simp only [map_add, adjointSum_add, hx, hy]

end ScalarExtension

end OriginalSameStepLinearizationConjugation
end Hindman168
