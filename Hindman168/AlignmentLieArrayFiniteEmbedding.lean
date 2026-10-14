import Hindman168.AlignmentFiniteEvaluationSelection

/-! A single finite family of actual integer evaluations embeds all
coefficient arrays in a finite product of the original Lie algebra.
Each component respects the original bracket exactly. -/

namespace Hindman168

variable {σ R L : Type*} [Field R] [CharZero R] [LieRing L] [LieAlgebra R L]

omit [CharZero R] in
noncomputable def alignmentLieArrayFiniteEvaluation (S : Finset (σ → ℤ)) :
    alignmentLiePolynomialArrays σ R L →ₗ[R] (S → L) where
  toFun x u := alignmentLiePolynomialArraysEvaluation (fun j => (u.val j : R)) x
  map_add' x y := funext fun _ => map_add _ x y
  map_smul' r x := funext fun _ => map_smul _ r x

omit [CharZero R] in
theorem alignmentLieArrayFiniteEvaluation_bracket (S : Finset (σ → ℤ))
    (x y : alignmentLiePolynomialArrays σ R L) (u : S) :
    alignmentLieArrayFiniteEvaluation S ⁅x, y⁆ u =
      ⁅alignmentLieArrayFiniteEvaluation S x u,
        alignmentLieArrayFiniteEvaluation S y u⁆ :=
  (alignmentLiePolynomialArraysEvaluation (fun j => (u.val j : R))).map_lie x y

theorem alignmentLieArrayFiniteEvaluation_exists_injective [Finite σ]
    [FiniteDimensional R L] {s : ℕ}
    (hs : LieModule.lowerCentralSeries R L L s = ⊥) :
    ∃ S : Finset (σ → ℤ), Function.Injective
      (alignmentLieArrayFiniteEvaluation (R := R) (L := L) S) := by
  obtain ⟨S, hS⟩ := alignmentLiePolynomialArrays_finite_integer_evaluations
    (σ := σ) hs
  refine ⟨S, fun x y hxy => sub_eq_zero.mp (hS (x - y) fun u hu => ?_)⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun hxy ⟨u, hu⟩)

end Hindman168
