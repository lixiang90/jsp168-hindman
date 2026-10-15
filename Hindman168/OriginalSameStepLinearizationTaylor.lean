import OAI.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
import OAI.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution

/-!
# Finite Taylor expansion for polynomial translation

The coefficients of the polynomial path `t ↦ p(X + t h)` are the iterated
directional derivatives divided by factorials.  Extending this identity
through the tensor product gives a finite Taylor formula for vector-valued
polynomials.  If the `N`th derivative vanishes, the formula stops at `N`.

Everything here is algebraic: the argument uses finite polynomial sums,
without an infinite exponential or an analytic convergence hypothesis.
-/

namespace Hindman168.OriginalSameStepLinearization

open OAI.Erdos3 OAI.Erdos3.VectorPolynomial
open scoped TensorProduct

section ScalarTaylor

variable {σ : Type*} [Fintype σ]

theorem scalarDirectionalDerivative_neg_direction (h : σ → ℚ)
    (p : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (-h) p = - scalarDirectionalDerivative h p := by
  simp only [scalarDirectionalDerivative_apply, Pi.neg_apply, neg_smul,
    Finset.sum_neg_distrib]

theorem positiveTranslationPath_derivative (h : σ → ℚ) (p : MvPolynomial σ ℚ) :
    (polynomialTranslationPath (-h) p).derivative =
      polynomialTranslationPath (-h) (scalarDirectionalDerivative h p) := by
  rw [polynomialTranslationPath_derivative, scalarDirectionalDerivative_neg_direction,
    map_neg, neg_neg]

theorem positiveTranslationPath_iterate_derivative (h : σ → ℚ)
    (p : MvPolynomial σ ℚ) (n : ℕ) :
    Polynomial.derivative^[n] (polynomialTranslationPath (-h) p) =
      polynomialTranslationPath (-h) ((scalarDirectionalDerivative h)^[n] p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, positiveTranslationPath_derivative]
    rw [Function.iterate_succ_apply']

theorem positiveTranslationPath_coeff (h : σ → ℚ) (p : MvPolynomial σ ℚ) (n : ℕ) :
    (polynomialTranslationPath (-h) p).coeff n =
      (n.factorial : ℚ)⁻¹ • ((scalarDirectionalDerivative h)^[n] p) := by
  have hc := Polynomial.coeff_iterate_derivative (k := n)
    (polynomialTranslationPath (-h) p) 0
  rw [positiveTranslationPath_iterate_derivative, Polynomial.coeff_zero_eq_eval_zero,
    polynomialTranslationPath_eval_zero] at hc
  simp only [Nat.zero_add, Nat.descFactorial_self] at hc
  rw [hc, ← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀]
  exact_mod_cast Nat.factorial_ne_zero n

theorem polynomialTranslate_eq_sum_range (h : σ → ℚ) (p : MvPolynomial σ ℚ)
    {N : ℕ} (hN : (polynomialTranslationPath (-h) p).natDegree < N) :
    polynomialTranslate h p = ∑ n ∈ Finset.range N,
      (n.factorial : ℚ)⁻¹ • ((scalarDirectionalDerivative h)^[n] p) := by
  have he := Polynomial.eval_eq_sum_range' hN (1 : MvPolynomial σ ℚ)
  have ht := polynomialTranslationPath_eval (-h) 1 p
  simp only [MvPolynomial.C_1, Pi.neg_apply, one_mul, neg_neg] at ht
  rw [ht] at he
  simpa only [one_pow, mul_one, positiveTranslationPath_coeff] using he

end ScalarTaylor

section TensorTaylor

variable {σ V : Type*} [Fintype σ] [AddCommGroup V] [Module ℚ V]

omit [Fintype σ] in
theorem rTensor_pow_tmul (f : Module.End ℚ (MvPolynomial σ ℚ))
    (p : MvPolynomial σ ℚ) (v : V) (n : ℕ) :
    ((f.rTensor V : Module.End ℚ (VectorPolynomial σ ℚ V)) ^ n) (p ⊗ₜ[ℚ] v) =
      ((f ^ n) p) ⊗ₜ[ℚ] v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply, ih, LinearMap.rTensor_tmul]

theorem exists_tensorTaylor (h : σ → ℚ) (p : VectorPolynomial σ ℚ V) :
    ∃ N : ℕ, ∀ m ≥ N,
      (polynomialTranslate h).toLinearMap.rTensor V p =
        ∑ n ∈ Finset.range m, (n.factorial : ℚ)⁻¹ •
          (((scalarDirectionalDerivative h).toLinearMap.rTensor V :
            Module.End ℚ (VectorPolynomial σ ℚ V)) ^ n) p := by
  induction p using TensorProduct.induction_on with
  | zero =>
    exact ⟨0, fun m _ => by simp⟩
  | tmul q v =>
    refine ⟨(polynomialTranslationPath (-h) q).natDegree + 1, ?_⟩
    intro m hm
    simp_rw [rTensor_pow_tmul]
    change polynomialTranslate h q ⊗ₜ[ℚ] v = _
    rw [polynomialTranslate_eq_sum_range h q (N := m) (by omega), TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul', Module.End.pow_apply]
    rfl
  | add p q hp hq =>
    obtain ⟨Np, hp⟩ := hp
    obtain ⟨Nq, hq⟩ := hq
    refine ⟨max Np Nq, ?_⟩
    intro m hm
    rw [map_add, hp m (le_trans (le_max_left _ _) hm),
      hq m (le_trans (le_max_right _ _) hm)]
    simp only [map_add, smul_add, Finset.sum_add_distrib]

theorem tensorTaylor_of_nilpotent (h : σ → ℚ) (p : VectorPolynomial σ ℚ V) (N : ℕ)
    (hN : (((scalarDirectionalDerivative h).toLinearMap.rTensor V :
      Module.End ℚ (VectorPolynomial σ ℚ V)) ^ N) p = 0) :
    (polynomialTranslate h).toLinearMap.rTensor V p =
      ∑ n ∈ Finset.range N, (n.factorial : ℚ)⁻¹ •
        (((scalarDirectionalDerivative h).toLinearMap.rTensor V :
          Module.End ℚ (VectorPolynomial σ ℚ V)) ^ n) p := by
  obtain ⟨M, hM⟩ := exists_tensorTaylor h p
  rw [hM (max M N) (le_max_left _ _)]
  symm
  apply Finset.sum_subset (Finset.range_mono (le_max_right M N))
  intro n hn hnN
  rw [Module.End.pow_map_zero_of_le (f :=
    (scalarDirectionalDerivative h).toLinearMap.rTensor V)
    (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hnN)) hN, smul_zero]

end TensorTaylor

section VectorTaylor

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem directionalDerivative_eq_scalar_rTensor {σ : Type*} [Fintype σ]
    (h : σ → ℚ) :
    (directionalDerivative h : Module.End ℚ (VectorPolynomial σ ℚ L)) =
      (scalarDirectionalDerivative h).toLinearMap.rTensor L := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro p
  apply LinearMap.ext
  intro x
  change directionalDerivative h (p ⊗ₜ[ℚ] x) =
    (scalarDirectionalDerivative h).toLinearMap.rTensor L (p ⊗ₜ[ℚ] x)
  rw [directionalDerivative_tmul, LinearMap.rTensor_tmul]
  change (∑ i, h i • (MvPolynomial.pderiv i p ⊗ₜ[ℚ] x)) =
    scalarDirectionalDerivative h p ⊗ₜ[ℚ] x
  rw [scalarDirectionalDerivative_apply, TensorProduct.sum_tmul]
  simp only [TensorProduct.smul_tmul']

theorem translate_eq_sum_of_nilpotent {σ : Type*} [Fintype σ]
    (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) (N : ℕ)
    (hN : ((directionalDerivative h : Module.End ℚ (VectorPolynomial σ ℚ L)) ^ N) p = 0) :
    translate h p = ∑ n ∈ Finset.range N, (n.factorial : ℚ)⁻¹ •
      ((directionalDerivative h : Module.End ℚ (VectorPolynomial σ ℚ L)) ^ n) p := by
  rw [directionalDerivative_eq_scalar_rTensor] at hN ⊢
  exact tensorTaylor_of_nilpotent h p N hN

end VectorTaylor

end Hindman168.OriginalSameStepLinearization
