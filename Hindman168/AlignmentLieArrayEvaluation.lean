import Hindman168.AlignmentLieArrayFiniteDimension
import Mathlib.Algebra.MvPolynomial.Eval

/-! Evaluation of the actual coefficient arrays is a Lie homomorphism to
the original Lie algebra, with the literal polynomial evaluation formula. -/

namespace Hindman168
open scoped TensorProduct

variable {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

noncomputable def alignmentLieArrayEvaluation (u : σ → R) :
    (MvPolynomial σ R ⊗[R] L) →ₗ⁅R⁆ L where
  __ := TensorProduct.lift ((LinearMap.lsmul R L).comp
    (MvPolynomial.aeval u).toLinearMap)
  map_lie' := by
    intro x y
    let f := TensorProduct.lift ((LinearMap.lsmul R L).comp
      (MvPolynomial.aeval u).toLinearMap)
    change f ⁅x, y⁆ = ⁅f x, f y⁆
    induction x using TensorProduct.induction_on with
    | zero => simp only [zero_lie y, map_zero, zero_lie]
    | tmul p a =>
        induction y using TensorProduct.induction_on with
        | zero => simp only [lie_zero (p ⊗ₜ[R] a), map_zero, lie_zero]
        | tmul q b =>
            simp only [f, LieAlgebra.ExtendScalars.bracket_tmul, TensorProduct.lift.tmul,
              LinearMap.comp_apply, LinearMap.lsmul_apply, smul_lie, lie_smul]
            change MvPolynomial.aeval u (p * q) • ⁅a, b⁆ =
              MvPolynomial.aeval u q • MvPolynomial.aeval u p • ⁅a, b⁆
            rw [map_mul, mul_comm, mul_smul]
        | add y z hy hz =>
            simp only [lie_add (p ⊗ₜ[R] a) y z, map_add, hy, hz, lie_add]
    | add x z hx hz =>
        simp only [add_lie x z y, map_add, hx, hz, add_lie]

theorem alignmentLieArrayEvaluation_tmul (u : σ → R) (p : MvPolynomial σ R) (x : L) :
    alignmentLieArrayEvaluation u (p ⊗ₜ[R] x) = MvPolynomial.aeval u p • x := rfl

theorem alignmentLieArrayEvaluation_monomial (u : σ → R) (d : σ →₀ ℕ) (x : L) :
    alignmentLieArrayEvaluation u (MvPolynomial.monomial d (1 : R) ⊗ₜ[R] x) =
      d.prod (fun j n => u j ^ n) • x := by
  rw [alignmentLieArrayEvaluation_tmul, MvPolynomial.aeval_monomial,
    map_one, one_mul]

noncomputable def alignmentLiePolynomialArraysEvaluation (u : σ → R) :
    alignmentLiePolynomialArrays σ R L →ₗ⁅R⁆ L :=
  (alignmentLieArrayEvaluation u).comp (alignmentLiePolynomialArrays σ R L).incl

theorem alignmentLiePolynomialArraysEvaluation_lowerCentral {s : ℕ}
    (u : σ → R) {x : alignmentLiePolynomialArrays σ R L}
    (hx : x ∈ LieModule.lowerCentralSeries R (alignmentLiePolynomialArrays σ R L)
      (alignmentLiePolynomialArrays σ R L) s) :
    alignmentLiePolynomialArraysEvaluation u x ∈ LieModule.lowerCentralSeries R L L s :=
  LieIdeal.map_lowerCentralSeries_le s (LieIdeal.mem_map hx)

end Hindman168
