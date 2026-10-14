import Hindman168.RoughNativeRealBoxBasisTransfer
import Hindman168.RoughHorizontalIntegerSize

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical Manifold ContDiff

variable {κ ι E : Type*} [Fintype κ] [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_real_box_coordinate_horizontal_transfer (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (b0 : Module.Basis ι ℝ E)
    (S : Finset ι)
    (hS : ∀ i, i ∉ S → b0 i ∈ nativeLieLowerCentralModel (I := I) (G := G) 1) (q : ℕ) (c C B η Mchar Acoeff : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (hMchar : 0 ≤ Mchar) (hAcoeff : 0 ≤ Acoeff) :
    ∃ A' Z0 : ℝ, 0 < A' ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ lo hi : κ → ℝ, (∀ j, c*Z ≤ hi j-lo j) →
      (∀ j, -C*Z ≤ lo j) → (∀ j, hi j ≤ C*Z) →
      ∀ (p : RoughVectorMvPolynomial (Option κ) E) (z : ℝ), RoughVectorMvDegreeLE p q →
      ∀ (f : (κ → ℤ) → ℂ) (mean : ℂ), (∀ x, ‖f x‖ ≤ B) →
      (∀ (N : ℕ) (b : κ → ℤ), 0 < N →
        η/2 ≤ ‖finiteComplexSetMean (Fintype.piFinset (fun _ : κ => Finset.range N))
          (fun v => f (fun j => b j+(v j : ℤ)))-mean‖ →
        ∃ χ : E →L[ℝ] ℝ, (∃ m : ι → ℤ, (∀ i ∈ S, χ (b0 i) = (m i : ℝ)) ∧
            roughHorizontalIntegerSize S m ≤ Mchar) ∧
          RoughNativeHorizontalFunctional (E := E) (I := I) Γ χ.toLinearMap ∧
          ∃ (α : (κ → ℕ) → ℝ) (c0 : ℝ),
            roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1)
              (roughScalarSpatialProjection χ.toLinearMap p z) =
                MvPolynomial.C c0+∑ J ∈ roughSpatialDegreeIndices κ q,
                  MvPolynomial.C (α J)*roughMvBinomialPolynomial J ∧
            ∀ J ∈ roughSpatialDegreeIndices κ q,
              ‖(α J : UnitAddCircle)‖ ≤ Acoeff*(N : ℝ)⁻¹^(∑ j, J j)) →
      η ≤ ‖finiteComplexSetMean (roughRealIntegerBox lo hi) f-mean‖ →
      ∃ χ ∈ roughNativeHorizontalCharacterGrid (E := E) (I := I) Γ (roughBasisOperatorNormBudget b0*Mchar),
        ∀ J : κ → ℕ, 0 < (∑ j, J j) →
        ‖((coeff (Finsupp.equivFunOnFinite.symm J)
          (roughScalarSpatialProjection ((roughBinomialMultiplier κ q : ℝ) • χ) p z) : ℝ) :
          UnitAddCircle)‖ ≤ A'*Z⁻¹^(∑ j, J j) := by
  obtain ⟨A', Z0, hA', hZ0, hbox⟩ := rough_native_real_box_basis_horizontal_transfer
    (κ := κ) (E := E) (I := I) Γ b0 q c C B η Mchar Acoeff
    hc hC hB hη hMchar hAcoeff
  refine ⟨A', Z0, hA', hZ0, ?_⟩
  intro Z hZ lo hi hlen hlo hhi p z hp f mean hf hinput hbad
  apply hbox Z hZ lo hi hlen hlo hhi p z hp f mean hf _ hbad
  intro N b hN hgap
  obtain ⟨χ, ⟨m, hm, hsize⟩, hhor, α, c0, he, hcoeff⟩ := hinput N b hN hgap
  exact ⟨χ, rough_basis_horizontal_integer_square_values_bound b0 S _ hS χ.toLinearMap
    hhor.2.1 m hm Mchar hMchar
      ((rough_horizontal_integer_size_le_iff S m Mchar hMchar).mp hsize),
    hhor, α, c0, he, hcoeff⟩

end Hindman168
