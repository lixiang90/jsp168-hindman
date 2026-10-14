import Hindman168.AlignmentCoefficientInputShift

namespace Hindman168
open scoped TensorProduct

variable {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

theorem alignmentLieArrayInputShift_add (v w : σ → R)
    (z : MvPolynomial σ R ⊗[R] L) :
    alignmentLieArrayInputShift v (alignmentLieArrayInputShift w z) =
      alignmentLieArrayInputShift (v + w) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p x =>
    change alignmentCoefficientInputShift v (alignmentCoefficientInputShift w p) ⊗ₜ[R] x = _
    rw [← AlgHom.comp_apply, alignmentCoefficientInputShift_add]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem alignmentLieArrayInputShift_zero (z : MvPolynomial σ R ⊗[R] L) :
    alignmentLieArrayInputShift (0 : σ → R) z = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul p x =>
    change alignmentCoefficientInputShift (0 : σ → R) p ⊗ₜ[R] x = _
    rw [alignmentCoefficientInputShift_zero]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem alignmentLieArrayInputShift_evaluation (v u : σ → R)
    (z : MvPolynomial σ R ⊗[R] L) :
    alignmentLieArrayEvaluation u (alignmentLieArrayInputShift v z) =
      alignmentLieArrayEvaluation (u + v) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p x =>
    change MvPolynomial.aeval u (alignmentCoefficientInputShift v p) • x = _
    rw [alignmentCoefficientInputShift_eval]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

noncomputable def alignmentLiePolynomialTranslation [Nontrivial R] (v : σ → R) :
    alignmentLiePolynomialArrays σ R L →ₗ⁅R⁆ alignmentLiePolynomialArrays σ R L where
  toFun x := ⟨alignmentLieArrayInputShift v x.val, alignmentLieArrayInputShift_mem v _ x.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)
  map_lie' {_ _} := Subtype.ext (LieHom.map_lie _ _ _)

theorem alignmentLiePolynomialTranslation_add [Nontrivial R] (v w : σ → R)
    (x : alignmentLiePolynomialArrays σ R L) :
    alignmentLiePolynomialTranslation v (alignmentLiePolynomialTranslation w x) =
      alignmentLiePolynomialTranslation (v + w) x :=
  Subtype.ext (alignmentLieArrayInputShift_add v w x.val)

theorem alignmentLiePolynomialTranslation_zero [Nontrivial R]
    (x : alignmentLiePolynomialArrays σ R L) :
    alignmentLiePolynomialTranslation (0 : σ → R) x = x :=
  Subtype.ext (alignmentLieArrayInputShift_zero x.val)

noncomputable def alignmentLiePolynomialTranslationEquiv [Nontrivial R] (v : σ → R) :
    alignmentLiePolynomialArrays σ R L ≃ₗ⁅R⁆ alignmentLiePolynomialArrays σ R L where
  __ := alignmentLiePolynomialTranslation v
  invFun := alignmentLiePolynomialTranslation (-v)
  left_inv x := by
    change alignmentLiePolynomialTranslation (-v) (alignmentLiePolynomialTranslation v x) = x
    rw [alignmentLiePolynomialTranslation_add, neg_add_cancel, alignmentLiePolynomialTranslation_zero]
  right_inv x := by
    change alignmentLiePolynomialTranslation v (alignmentLiePolynomialTranslation (-v) x) = x
    rw [alignmentLiePolynomialTranslation_add, add_neg_cancel, alignmentLiePolynomialTranslation_zero]

theorem alignmentLiePolynomialTranslation_evaluation [Nontrivial R] (v u : σ → R)
    (x : alignmentLiePolynomialArrays σ R L) :
    alignmentLiePolynomialArraysEvaluation u (alignmentLiePolynomialTranslation v x) =
      alignmentLiePolynomialArraysEvaluation (u + v) x :=
  alignmentLieArrayInputShift_evaluation v u x.val

end Hindman168

