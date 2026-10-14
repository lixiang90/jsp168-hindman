import Hindman168.NativeOriginalAffineCubeInput
import Hindman168.RoughNativeRealBoxHorizontalTransfer
import Hindman168.NativeFilteredHorizontalMultiplier

/-! The actual corrected real-box consequence for the ORIGINAL arbitrary-step native
nilmanifold. No translated-cube inverse or character-production hypothesis remains. -/

namespace Hindman168
open MeasureTheory MvPolynomial
open scoped Classical BigOperators Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_original_real_box_finite_obstruction
    {s : ℕ} (D : NativeNilmanifoldData.{u} s) (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ S : Finset (D.E →ₗ[ℝ] ℝ),
      (∀ χ ∈ S, RoughNativeHorizontalFunctional (I := D.I) D.Γ χ) ∧
      ∃ A' Z0 : ℝ, 0 < A' ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
        ∀ lo hi : Fin n → ℝ, (∀ j, c*Z ≤ hi j-lo j) →
        (∀ j, -C*Z ≤ lo j) → (∀ j, hi j ≤ C*Z) →
        ∀ (Q : (Option (Fin n) → ℝ) → D.G) (p : RoughVectorMvPolynomial (Option (Fin n)) D.E),
          RoughVectorMvDegreeLE p d →
          (∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x) = roughVectorMvEval p x) →
          ∀ z : ℝ, ∀ F : C(D.G ⧸ D.Γ, ℂ), LipschitzWith L F → (∀ q, ‖F q‖ ≤ B) →
            η ≤ ‖finiteComplexSetMean (roughRealIntegerBox lo hi)
              (fun x => F (Q (fun i => i.elim z (fun j => (x j : ℝ))) : D.G ⧸ D.Γ)) -
                ∫ q, F q ∂nativeNilmanifoldQuotientProbability D‖ →
            ∃ χ ∈ S, ∀ J : Fin n → ℕ, 0 < (∑ j, J j) →
              ‖((coeff (Finsupp.equivFunOnFinite.symm J)
                (roughScalarSpatialProjection χ p z) : ℝ) : UnitAddCircle)‖ ≤ A'*Z⁻¹^(∑ j, J j) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨M, _, hcube⟩ := native_original_affine_cube_binomial_input D n d B L (η/2) (by positivity)
  let grid := roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (M : ℝ)
  let K := roughBinomialMultiplier (Fin n) d
  let S := grid.image (fun χ => (K : ℝ) • χ)
  have hK : 0 < K := rough_binomial_multiplier_positive (Fin n) d
  obtain ⟨A', Z0, hA', hZ0, hbox⟩ := rough_native_real_box_horizontal_transfer
    (κ := Fin n) (I := D.I) D.Γ d c C B η (M : ℝ) (M : ℝ)
    hc hC hB hη (Nat.cast_nonneg M) (Nat.cast_nonneg M)
  refine ⟨S, ?_, A', Z0, hA', hZ0, ?_⟩
  · intro χ hχ
    obtain ⟨χ0, hχ0, rfl⟩ := Finset.mem_image.mp hχ
    exact native_filtered_horizontal_natural_multiple (I := D.I) D.Γ χ0
      ((rough_native_horizontal_grid_mem_iff (I := D.I) D.Γ (M : ℝ) χ0).mp hχ0).2 K hK
  · intro Z hZ lo hi hlen hlo hhi Q p hp hQ z F hF hbound hbad
    let f := fun x : Fin n → ℤ => F (Q (fun i => i.elim z (fun j => (x j : ℝ))) : D.G ⧸ D.Γ)
    have hf : ∀ x, ‖f x‖ ≤ B := fun x => hbound _
    have hinput : ∀ (N : ℕ) (b : Fin n → ℤ), 0 < N →
        η/2 ≤ ‖finiteComplexSetMean (Fintype.piFinset (fun _ : Fin n => Finset.range N))
          (fun v => f (fun j => b j+(v j : ℤ))) - ∫ q, F q ∂nativeNilmanifoldQuotientProbability D‖ →
        ∃ χ : D.E →L[ℝ] ℝ, ‖χ‖ ≤ (M : ℝ) ∧
          RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧
          ∃ (α : (Fin n → ℕ) → ℝ) (c0 : ℝ),
            roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1)
              (roughScalarSpatialProjection χ.toLinearMap p z) =
                MvPolynomial.C c0+∑ J ∈ roughSpatialDegreeIndices (Fin n) d,
                  MvPolynomial.C (α J)*roughMvBinomialPolynomial J ∧
            ∀ J ∈ roughSpatialDegreeIndices (Fin n) d,
              ‖(α J : UnitAddCircle)‖ ≤ (M : ℝ)*(N : ℝ)⁻¹^(∑ j, J j) := by
      intro N b hN hgap
      exact hcube Q p hp hQ z b N hN F hF hbound hgap
    obtain ⟨χ, hχ, hcoeff⟩ := hbox Z hZ lo hi hlen hlo hhi p z hp f
      (∫ q, F q ∂nativeNilmanifoldQuotientProbability D) hf (by
        intro N b hN hgap
        have hpi : @Fintype.piFinset (Fin n) (fun a b => Classical.propDecidable (a=b))
            (Fin.fintype n) (fun _ => ℕ) (fun _ => Finset.range N) =
            @Fintype.piFinset (Fin n) (instDecidableEqFin n) (Fin.fintype n)
              (fun _ => ℕ) (fun _ => Finset.range N) := by
          ext v
          simp only [Fintype.mem_piFinset]
        rw [hpi] at hgap
        exact hinput N b hN hgap) hbad
    exact ⟨(K : ℝ) • χ, Finset.mem_image.mpr ⟨χ, hχ, rfl⟩, hcoeff⟩

end Hindman168
