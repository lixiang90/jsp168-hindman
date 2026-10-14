import Hindman168.AlignmentLieArrayEvaluation
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Integer evaluations determine the actual polynomial Lie coefficients.
The argument separates coefficients in a basis of the original Lie algebra
and uses polynomial extensionality on the infinite integer box. -/

namespace Hindman168
open scoped TensorProduct

variable {σ R L ι : Type*} [Field R] [CharZero R] [LieRing L] [LieAlgebra R L]

omit [CharZero R] in
theorem alignmentLieArrayEvaluation_basis_coefficient [DecidableEq ι] (b : Module.Basis ι R L)
    (u : σ → R) (x : MvPolynomial σ R ⊗[R] L) (i : ι) :
    MvPolynomial.eval u ((TensorProduct.equivFinsuppOfBasisRight b) x i) =
      b.repr (alignmentLieArrayEvaluation u x) i := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | tmul p a =>
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        alignmentLieArrayEvaluation_tmul]
      simp only [map_smul, Finsupp.smul_apply,
        MvPolynomial.aeval_eq_eval, smul_eq_mul, mul_comm]
      change MvPolynomial.aeval u (b.repr a i • p) =
        b.repr a i * MvPolynomial.aeval u p
      rw [map_smul, smul_eq_mul]
  | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, hx, hy]

theorem alignmentLieArray_zero_of_integer_evaluations
    (b : Module.Basis ι R L) (x : MvPolynomial σ R ⊗[R] L)
    (hx : ∀ u : σ → ℤ, alignmentLieArrayEvaluation (fun j => (u j : R)) x = 0) :
    x = 0 := by
  classical
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  rw [map_zero]
  apply Finsupp.ext
  intro i
  change (TensorProduct.equivFinsuppOfBasisRight b) x i = 0
  apply MvPolynomial.funext_set (fun _ => Set.range (fun n : ℤ => (n : R)))
    (fun _ => Set.infinite_range_of_injective Int.cast_injective)
  intro u hu
  have hchoice : ∀ j, ∃ n : ℤ, (n : R) = u j :=
    fun j => hu j (Set.mem_univ j)
  choose z hz using hchoice
  have hzu : (fun j => (z j : R)) = u := funext hz
  rw [← hzu, alignmentLieArrayEvaluation_basis_coefficient, hx z,
    map_zero, Finsupp.zero_apply, map_zero]

theorem alignmentLieArray_integer_evaluations_injective :
    Function.Injective (fun x : MvPolynomial σ R ⊗[R] L =>
      fun u : σ → ℤ => alignmentLieArrayEvaluation (fun j => (u j : R)) x) := by
  intro x y h
  apply sub_eq_zero.mp
  apply alignmentLieArray_zero_of_integer_evaluations (Module.Free.chooseBasis R L)
  intro u
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun h u)

end Hindman168
