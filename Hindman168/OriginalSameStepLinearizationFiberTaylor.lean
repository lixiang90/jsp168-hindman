import Hindman168.OriginalSameStepLinearizationTranslation
import Hindman168.OriginalSameStepLinearizationTaylor

/-!
# Finite Taylor expansion on the first shifted polynomial ideal

Each derivative raises the coefficient-filtration index by one. On the first
shifted ideal for an `s`-step filtration, the `s`th derivative vanishes.
Consequently translation is the exponential sum with exactly `s` terms.
-/

namespace Hindman168.OriginalSameStepLinearization

open OAI.Erdos3 OAI.Erdos3.VectorPolynomial
open scoped TensorProduct

section FiberTaylor

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem derivative_pow_polynomial (d : ℕ) (h : Fin d → ℚ) (p : Fiber F d)
    (n : ℕ) :
    ((((derivative F d h).toLinearMap : Module.End ℚ (Fiber F d)) ^ n) p).val.val =
      ((directionalDerivative h : Module.End ℚ (VectorPolynomial (Fin d) ℚ L)) ^ n)
        p.val.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply]
    change directionalDerivative h _ = directionalDerivative h _
    exact congrArg (directionalDerivative h) ih

theorem derivative_pow_mem_shifted (d : ℕ) (h : Fin d → ℚ) (p : Fiber F d)
    (n : ℕ) :
    ((((derivative F d h).toLinearMap : Module.End ℚ (Fiber F d)) ^ n) p).val ∈
      F.shiftedPolynomialIdeal (fun _ => 1) (n + 1) := by
  induction n with
  | zero => exact p.property
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply]
    exact Calculus.adaptedDirectionalDerivative_mem_shifted F h (n + 1) ih

theorem derivative_pow_eq_zero (d : ℕ) (h : Fin d → ℚ) (p : Fiber F d)
    (n : ℕ) (hn : s ≤ n) :
    (((derivative F d h).toLinearMap : Module.End ℚ (Fiber F d)) ^ n) p = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  change ((((derivative F d h).toLinearMap : Module.End ℚ (Fiber F d)) ^ n) p).val.val =
    (0 : VectorPolynomial (Fin d) ℚ L)
  apply coefficients.injective
  ext α
  have hm := derivative_pow_mem_shifted F d h p n α
  have ht := F.antitone (show s + 1 ≤ Finsupp.weight (fun _ : Fin d => 1) α + (n + 1)
    by omega) hm
  change coefficients
    ((((derivative F d h).toLinearMap : Module.End ℚ (Fiber F d)) ^ n) p).val.val α ∈
      F.layer (s + 1) at ht
  rw [F.terminal, Submodule.mem_bot] at ht
  simpa only [map_zero, Finsupp.zero_apply] using ht

theorem directionalDerivative_pow_eq_zero (d : ℕ) (h : Fin d → ℚ)
    (p : Fiber F d) (n : ℕ) (hn : s ≤ n) :
    ((directionalDerivative h : Module.End ℚ (VectorPolynomial (Fin d) ℚ L)) ^ n)
      p.val.val = 0 := by
  have hz := congrArg (fun q : Fiber F d => q.val.val)
    (derivative_pow_eq_zero F d h p n hn)
  change _ = (0 : VectorPolynomial (Fin d) ℚ L) at hz
  simpa only [derivative_pow_polynomial] using hz

/-- Translation is the finite exponential of its infinitesimal derivative.
The first shifted ideal needs exactly `s` terms for an `s`-step filtration. -/
theorem fiberTranslation_eq_sum (d : ℕ) (h : Fin d → ℚ) (p : Fiber F d) :
    fiberTranslation F d h p = ∑ n ∈ Finset.range s,
      (n.factorial : ℚ)⁻¹ •
        (((derivative F d h).toLinearMap : Module.End ℚ (Fiber F d)) ^ n) p := by
  have hn := directionalDerivative_pow_eq_zero F d h p s le_rfl
  have ht := translate_eq_sum_of_nilpotent h p.val.val s hn
  apply Subtype.ext
  apply Subtype.ext
  simpa only [fiberTranslation_val, adaptedTranslation_val,
    AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, derivative_pow_polynomial] using ht


end FiberTaylor

end Hindman168.OriginalSameStepLinearization
