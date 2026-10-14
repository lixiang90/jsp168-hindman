import Hindman168.NativeOriginalBadPairCharacters
import Hindman168.RoughNativeRealBadIndexComplex

/-! ACTUAL real bad pairs retain EXACT original discrepancy in the proved
complex production theorem; ALL original affine rows and fixed budget survive. -/
namespace Hindman168
open MeasureTheory MvPolynomial
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_original_real_bad_pair_characters {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ S : Finset (D.E →ₗ[ℝ] ℝ),
      (∀ χ ∈ S, RoughNativeHorizontalFunctional (I := D.I) D.Γ χ) ∧
      ∃ A Z0 : ℝ, 0 < A ∧ 1 ≤ Z0 ∧
      ∀ (t : ℕ), 0 < t → ∀ Z : ℝ, Z0 ≤ Z → Z0 ≤ Z/t →
        (t : ℝ) ≤ Z → (t : ℝ) ≤ (c/2)*Z →
      ∀ (Q : (Option (Fin n) → ℝ) → D.G) (p : RoughVectorMvPolynomial (Option (Fin n)) D.E),
        RoughVectorMvDegreeLE p d →
        (∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x) = roughVectorMvEval p x) →
      ∀ z : ℕ, RoughNativeBadIndex D Q z t Z c C L B η →
        ∃ χ ∈ S, ∃ pOb : ℕ, ∃ bOb : Fin n → ℕ,
          (pOb=1 ∨ pOb=t) ∧ (∀ j, bOb j ≤ pOb) ∧
          ∀ J : Fin n → ℕ, 0 < (∑ j, J j) →
            ‖((coeff (Finsupp.equivFunOnFinite.symm J)
              (roughMvAffineSubstitution (fun j => (bOb j : ℝ)) (fun _ => (pOb : ℝ))
                (roughScalarSpatialProjection χ p (z : ℝ))) : ℝ) : UnitAddCircle)‖ ≤
                  A*((pOb : ℝ)/Z)^(∑ j, J j) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨S,hS,A,Z0,hA,hZ0,hProduce⟩ := native_original_bad_pair_characters D n d c C B η L hc hC hB hη
  refine ⟨S,hS,A,Z0,hA,hZ0,?_⟩
  intro t ht Z hZ hZt htZ htc Q p hp hQ z hBad
  exact hProduce t ht Z hZ hZt htZ htc Q p hp hQ z
    (rough_native_real_bad_index_complex D Q z t Z c C L B η hBad)

end Hindman168
