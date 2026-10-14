import Hindman168.NativeFilteredHorizontalGrid
import Hindman168.RoughNativeRealBoxBinomialTransfer

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical Manifold ContDiff

variable {κ E : Type*} [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_filtered_real_box_horizontal_transfer (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (q : ℕ) (c C B η Achar Acoeff : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (hAchar : 0 ≤ Achar) (hAcoeff : 0 ≤ Acoeff) :
    ∃ A' Z0 : ℝ, 0 < A' ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ lo hi : κ → ℝ, (∀ j, c*Z ≤ hi j-lo j) →
      (∀ j, -C*Z ≤ lo j) → (∀ j, hi j ≤ C*Z) →
      ∀ (p : RoughVectorMvPolynomial (Option κ) E) (z : ℝ), RoughVectorMvDegreeLE p q →
      ∀ (f : (κ → ℤ) → ℂ) (mean : ℂ), (∀ x, ‖f x‖ ≤ B) →
      (∀ (N : ℕ) (b : κ → ℤ), 0 < N →
        η/2 ≤ ‖finiteComplexSetMean (Fintype.piFinset (fun _ : κ => Finset.range N))
          (fun v => f (fun j => b j+(v j : ℤ)))-mean‖ →
        ∃ χ : E →L[ℝ] ℝ, nativeFilteredHorizontalCoefficientSize (I := I) Γ χ.toLinearMap ≤ Achar ∧
          RoughNativeHorizontalFunctional (E := E) (I := I) Γ χ.toLinearMap ∧
          ∃ (α : (κ → ℕ) → ℝ) (c0 : ℝ),
            roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1)
              (roughScalarSpatialProjection χ.toLinearMap p z) =
                MvPolynomial.C c0+∑ J ∈ roughSpatialDegreeIndices κ q,
                  MvPolynomial.C (α J)*roughMvBinomialPolynomial J ∧
            ∀ J ∈ roughSpatialDegreeIndices κ q,
              ‖(α J : UnitAddCircle)‖ ≤ Acoeff*(N : ℝ)⁻¹^(∑ j, J j)) →
      η ≤ ‖finiteComplexSetMean (roughRealIntegerBox lo hi) f-mean‖ →
      ∃ χ ∈ nativeFilteredSmoothBasisIntegerCharacterGrid (I := I) Γ ⌈Achar⌉₊,
        ∀ J : κ → ℕ, 0 < (∑ j, J j) →
        ‖((coeff (Finsupp.equivFunOnFinite.symm J)
          (roughScalarSpatialProjection ((roughBinomialMultiplier κ q : ℝ) • χ) p z) : ℝ) :
          UnitAddCircle)‖ ≤ A'*Z⁻¹^(∑ j, J j) := by
  obtain ⟨A', Z0, hA', hZ0, hbox⟩ := rough_native_real_box_binomial_transfer (κ := κ)
    (fun χ : E →ₗ[ℝ] ℝ => χ) (nativeFilteredSmoothBasisIntegerCharacterGrid (I := I) Γ ⌈Achar⌉₊)
    q c C B η Acoeff hc hC hB hη hAcoeff
  refine ⟨A', Z0, hA', hZ0, ?_⟩
  intro Z hZ lo hi hlen hlo hhi p z hp f mean hf hinput hbad
  apply hbox Z hZ lo hi hlen hlo hhi p z hp f mean hf _ hbad
  intro N b hN hgap
  obtain ⟨χ, hnorm, hhor, α, c0, he, hcoeff⟩ := hinput N b hN hgap
  exact ⟨χ.toLinearMap, native_filtered_horizontal_size_grid_contains (I := I) Γ Achar hAchar χ.toLinearMap hhor hnorm,
    α, c0, he, hcoeff⟩

end Hindman168
