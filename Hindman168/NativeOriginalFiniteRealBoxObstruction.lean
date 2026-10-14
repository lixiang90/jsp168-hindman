import Hindman168.NativeOriginalRealBoxObstruction
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The corrected real-box consequence is simultaneous over EVERY fixed
finite list of genuine native nilmanifolds, including the empty list.
Common constants precede every source, box, parameter and observable. -/
namespace Hindman168
open MeasureTheory MvPolynomial
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_original_finite_real_box_obstruction {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ S : ∀ i, Finset ((D i).E →ₗ[ℝ] ℝ),
      (∀ i, ∀ χ ∈ S i, RoughNativeHorizontalFunctional (I := (D i).I) (D i).Γ χ) ∧
      ∃ A' Z0 : ℝ, 0 < A' ∧ 1 ≤ Z0 ∧ ∀ i : ι,
        letI : MeasurableSpace (D i).E := borel (D i).E
        letI : MeasurableSpace (D i).G := borel (D i).G
        letI := (D i).metric
        letI : TopologicalSpace ((D i).G ⧸ (D i).Γ) := (D i).metric.toUniformSpace.toTopologicalSpace
        ∀ Z : ℝ, Z0 ≤ Z → ∀ lo hi : Fin n → ℝ,
          (∀ j, c*Z ≤ hi j-lo j) → (∀ j, -C*Z ≤ lo j) → (∀ j, hi j ≤ C*Z) →
          ∀ (Q : (Option (Fin n) → ℝ) → (D i).G)
            (p : RoughVectorMvPolynomial (Option (Fin n)) (D i).E),
            RoughVectorMvDegreeLE p d →
            (∀ x, nativeLieGlobalLogarithm (E := (D i).E) (I := (D i).I) (Q x) = roughVectorMvEval p x) →
            ∀ z : ℝ, ∀ F : C((D i).G ⧸ (D i).Γ, ℂ), LipschitzWith L F → (∀ q, ‖F q‖ ≤ B) →
              η ≤ ‖finiteComplexSetMean (roughRealIntegerBox lo hi)
                (fun x => F (Q (fun j => j.elim z (fun k => (x k : ℝ))) : (D i).G ⧸ (D i).Γ)) -
                  ∫ q, F q ∂nativeNilmanifoldQuotientProbability (D i)‖ →
              ∃ χ ∈ S i, ∀ J : Fin n → ℕ, 0 < (∑ j, J j) →
                ‖((coeff (Finsupp.equivFunOnFinite.symm J)
                  (roughScalarSpatialProjection χ p z) : ℝ) : UnitAddCircle)‖ ≤ A'*Z⁻¹^(∑ j, J j) := by
  have hEach (i : ι) := native_original_real_box_finite_obstruction (D i) n d c C B η L hc hC hB hη
  choose S hS A Zmin hA hZmin hData using hEach
  let R : ℝ := 1+∑ i, (A i+Zmin i)
  have hTerm (i : ι) : 0 ≤ A i+Zmin i := add_nonneg (hA i).le (zero_le_one.trans (hZmin i))
  have hR1 : 1 ≤ R := by
    have hs : (0 : ℝ) ≤ ∑ i, (A i+Zmin i) := Finset.sum_nonneg (fun i _ => hTerm i)
    dsimp only [R]
    linarith
  have hSum (i : ι) : A i+Zmin i ≤ R :=
    (Finset.single_le_sum (fun i _ => hTerm i) (Finset.mem_univ i)).trans
      (by dsimp only [R]; linarith)
  have hAR (i : ι) : A i ≤ R := (le_add_of_nonneg_right (zero_le_one.trans (hZmin i))).trans (hSum i)
  have hZR (i : ι) : Zmin i ≤ R := (le_add_of_nonneg_left (hA i).le).trans (hSum i)
  refine ⟨S,hS,R,R,zero_lt_one.trans_le hR1,hR1,?_⟩
  intro i
  letI : MeasurableSpace (D i).E := borel (D i).E
  letI : MeasurableSpace (D i).G := borel (D i).G
  letI := (D i).metric
  letI : TopologicalSpace ((D i).G ⧸ (D i).Γ) := (D i).metric.toUniformSpace.toTopologicalSpace
  intro Z hRZ lo hi hlen hlo hhi Q p hp hQ z F hF hbound hBad
  obtain ⟨χ,hχ,hCoeff⟩ := hData i Z ((hZR i).trans hRZ) lo hi hlen hlo hhi Q p hp hQ z F hF hbound hBad
  refine ⟨χ,hχ,?_⟩
  intro J hJ
  exact (hCoeff J hJ).trans (mul_le_mul_of_nonneg_right (hAR i)
    (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans (hR1.trans hRZ))) _))

end Hindman168
